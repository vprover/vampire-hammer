import VampireHammer.Replay.Symbols
import VampireHammer.Replay.Term
import VampireHammer.Replay.Diagnostics

/-!
Replay the topologically ordered proof DAG, share lazy CNF candidates, and dispatch each node
with its actual parents.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend

/-- Fixed inputs and the shared lazy CNF cache for one local refutation. -/
private structure ReplayContext where
  steps : Array Step
  derived : Array DerivedSymbol
  derivedByName : Std.HashMap String DerivedSymbol
  allSources : Array FVarId
  sourceProofs : Std.HashMap String Expr
  typeAtoms : Std.HashMap Nat Expr
  inhabitants : Array Expr
  cnfCache : IO.Ref (Std.HashMap String (Option (Array (Expr × Expr))))

/-- What ordinary reconstruction needs to know about the proof-local symbols
in scope. It changes only when a symbol or polarity-flip `let` is introduced,
so it is cached in `ReplayState` and keyed by the sizes of those tables. -/
private structure SymbolScope where
  key : Nat × Nat
  /-- Whether any proof-local symbol must stay folded. -/
  hasOpaque : Bool
  /-- Proof-local `let`s that ordinary rules may unfold. -/
  unfoldable : FVarIdSet
  avatarAtoms : Array Expr

/-- The DAG prefix already checked and the signature currently in scope.
Symbol-binding continuations retry the same index with an extended signature;
only a reconstructed node advances the index. -/
private structure ReplayState where
  index : Nat := 0
  replayed : Std.HashMap String StepProof := {}
  finalProof? : Option Expr := none
  flips : PolarityFlips
  termAtoms : Std.HashMap Nat Expr
  etoms : Std.HashMap Nat Expr
  symbols : Std.HashMap String Expr
  scope? : Option SymbolScope := none

/-- Named predicates and Skolem functions stay folded for ordinary rules.
Unfolding `sP x̄` into its body would, for example, make clause conversion see
the body's connectives as further literals, and unfolding a Skolem function
exposes a large `Classical.choose` term to `whnf`. AVATAR components unfold as
before. The handlers that introduce these symbols (definition, folding,
Skolemization) re-enable full unfolding. Flipped predicates stay folded too,
so `p_flipped t` remains one literal. -/
private def symbolScope (context : ReplayContext) (state : ReplayState) :
    MetaM SymbolScope := do
  let key := (state.symbols.size, state.flips.letFVars.size)
  if let some scope := state.scope? then
    if scope.key == key then return scope
  let mut opaqueSet : FVarIdSet := {}
  let mut avatarAtoms := #[]
  for symbol in context.derived do
    let some value := state.symbols.get? symbol.name | continue
    if symbol.kind == .avatarDefinition then
      avatarAtoms := avatarAtoms.push value
    else if symbol.kind == .predicateDefinition || symbol.kind == .skolem ||
        symbol.kind == .differenceWitness || symbol.kind == .quantifierWitness ||
        symbol.kind == .choiceOperator || symbol.kind == .differenceOperator then
      if let some fvarId := value.fvarId? then opaqueSet := opaqueSet.insert fvarId
  for flipped in state.flips.letFVars do
    if let some fvarId := flipped.fvarId? then opaqueSet := opaqueSet.insert fvarId
  let unfoldable := (← getLCtx).foldl (init := ({} : FVarIdSet)) fun set decl =>
    if decl.isLet && !opaqueSet.contains decl.fvarId then set.insert decl.fvarId else set
  pure { key, hasOpaque := !opaqueSet.isEmpty, unfoldable, avatarAtoms }

/-- Retrieve cited parents in certificate order. CNF candidates remain lazy
and are shared by siblings, including cached failures (`some none`). -/
private def collectParentProofs (context : ReplayContext) (state : ReplayState)
    (step : Step) : MetaM (Array ParentProof) := do
  let needsCnfBundle := step.inference?.any (·.rule == "cnf_transformation")
  let mut parentProofs : Array ParentProof := #[]
  for parentRef in step.parents do
    let some parent := state.replayed.get? parentRef.name
      | throwError "Vampire step `{step.name}` refers to unavailable parent `{parentRef.name}`"
    -- The `cnfify` candidates are computed only when a CNF step cannot be
    -- proved directly, and then once per parent: sibling CNF steps share them.
    let cnfCandidates : MetaM (Option (Array (Expr × Expr))) := do
      if !needsCnfBundle then return none
      if let some cached := (← context.cnfCache.get).get? parentRef.name then return cached
      let prepared ← BackendPreprocessing.prepareCnf parent.proof
      context.cnfCache.modify (·.insert parentRef.name prepared)
      pure prepared
    parentProofs := parentProofs.push
      { parent := parentRef
        binders := parent.step.binders
        existentialVariables := parent.step.existentialVariables
        componentBinders := parent.step.componentBinders
        target := parent.target
        clauseForm := parent.clauseForm
        clauseLiterals? := parent.clauseLiterals?
        cnfCandidates
        proof := parent.proof }
  pure parentProofs

/-- Translate an attached SAT trail only when an existing replay limit permits
it. The backend still checks every hint against its boundary clauses. -/
private def translateSatProof (context : ReplayContext) (state : ReplayState)
    (step : Step) : MetaM (Option (String × Array SatClause)) := do
  match step.satProof? with
  | some satProof => do
    let opts ← getOptions
    let limit := max (vampire.satReplayLimit.get opts) (vampire.satLratReplayLimit.get opts)
    if limit == 0 || satProof.steps.size > limit then pure none else do
      let clauses : Array SatClause ← satProof.steps.mapM fun satStep => do
        let literals ← ((flattenOr satStep.formula).filter
          (· != .base .falseE)).toArray.mapM (translateLocal context.typeAtoms state.termAtoms state.etoms)
        pure ⟨satStep.name, literals, satStep.parents, satStep.rule⟩
      pure (some (satProof.root, clauses))
  | none => pure none

/-- Reconstruct one node while preserving named predicates as clause atoms.
The diagnostic records only the failing node before rethrowing the error. -/
private def reconstructNode (scope : SymbolScope) (input : RuleInput) : MetaM Expr := do
  let reconstruct := if !scope.hasOpaque then Backend.reconstruct input else
    withConfig (fun config => { config with zetaDelta := false }) <|
      withZetaDeltaSet scope.unfoldable (Backend.reconstruct input)
  try reconstruct catch error =>
    -- The outer `run_elab` error can be a very large theorem.  Printing that
    -- theorem has previously exhausted Lean's diagnostic pretty-printer and
    -- hidden the useful local exception.  Record the node-local failure
    -- before propagating it to preserve the ordinary error behaviour.
    trace[vampire.replay] "reconstruction of {input.step.name} failed: {error.toMessageData}"
    throw error

/-- Check that a witness-introducing step cites exactly its witness parent
with a valid binder mapping, and return that parent. -/
private def witnessParent (state : ReplayState) (step : Step) (description : String)
    (parentName : String) (binderMapping? : Option (Array (String × String))) :
    MetaM StepProof := do
  unless step.parents.size == 1 && step.parents[0]?.any (·.name == parentName) do
    throwError "{description} `{step.name}` has an incorrect witness parent"
  let some parent := state.replayed[parentName]?
    | throwError "{description} `{step.name}` has an unavailable witness parent"
  unless (witnessBinderIndices? (parent.step.binders.map (·.name))
      (step.binders.map (·.name)) binderMapping?).isSome do
    throwError "{description} `{step.name}` has an invalid witness binder mapping"
  pure parent

/-- Introduce the proof-local `let` that `step` needs before it can be
translated, and replay the rest of the DAG (from the same index) inside its
scope through `resume`. Returns `none` when the step needs no new symbol. The
continuation structure keeps each `let` in scope for all later DAG nodes and
closes it with `mkLetFVars` in the completed local proof term. -/
private def introduceSymbols? (context : ReplayContext) (state : ReplayState) (step : Step)
    (resume : ReplayState → MetaM Expr) : MetaM (Option Expr) := do
  let derived := context.derivedByName
  let typeAtoms := context.typeAtoms
  let { termAtoms, etoms, symbols, flips, .. } := state
  let resumeWith := fun termAtoms etoms symbols =>
    resume { state with termAtoms, etoms, symbols }
  if flips.boundary? == some step.name then
    return some (← withPolarityFlipLets flips.heads 0 typeAtoms termAtoms etoms symbols #[]
      fun termAtoms etoms symbols letFVars =>
        resume { state with
          flips := { flips with boundary? := none, letFVars }, termAtoms, etoms, symbols })
  let some inference := step.inference? | return none
  if let some info := inference.avatarDefinition? then
    if !symbols.contains info.symbol then
      return some (← withAvatarDefinitionLet step info derived typeAtoms termAtoms etoms symbols
        resumeWith)
  if let some info := inference.predicateDefinition? then
    if !symbols.contains info.symbol then
      return some (← withPredicateDefinitionLet step info derived typeAtoms termAtoms etoms
        symbols resumeWith)
  if let some info := inference.negativeExtensionality? then
    unless symbols.contains info.symbol do
      let parent ← witnessParent state step "negative extensionality" info.literal.parent
        info.binderMapping?
      return some (← withDifferenceWitnessLet info parent derived typeAtoms termAtoms etoms
        symbols resumeWith)
  if let some info := inference.quantifierWitness? then
    if !info.introduce && !symbols.contains info.symbol then
      throwError "quantifier witness `{step.name}` reuses unbound `{info.symbol}`"
    unless symbols.contains info.symbol do
      let parent ← witnessParent state step "quantifier witness" info.literal.parent
        info.binderMapping?
      return some (← withQuantifierWitnessLet info parent derived typeAtoms termAtoms etoms
        symbols resumeWith)
  if let some info := inference.choiceAxiom? then
    if info.introduce && !symbols.contains info.symbol then
      unless step.parents.isEmpty do throwError "choice introduction `{step.name}` has unexpected parents"
      return some (← withChoiceOperatorLet info derived typeAtoms termAtoms etoms symbols
        resumeWith)
  if let some info := inference.functionalExtensionality? then
    if info.introduce && !symbols.contains info.symbol then
      unless step.parents.isEmpty do throwError "extensionality axiom `{step.name}` has unexpected parents"
      return some (← withDifferenceOperatorLet info derived typeAtoms termAtoms etoms symbols
        resumeWith)
  -- A not-yet-bound Skolem symbol must be introduced before translating this
  -- very step, because the conclusion already contains it.
  if let some info := inference.skolemization? then
    let unbound := info.bindings.filter fun binding => !symbols.contains binding.symbol
    if !unbound.isEmpty then
      unless unbound.size == info.bindings.size && step.parents.size == 1 do
        throwError "Skolemization `{step.name}` has partially bound symbols or not exactly one parent"
      let some parentRef := step.parents[0]? | throwError "Skolemization `{step.name}` has no parent"
      let some parent := state.replayed.get? parentRef.name
        | throwError "Skolemization `{step.name}` refers to unavailable parent `{parentRef.name}`"
      -- A parent reconstructed through the clause bridge has a
      -- `Clause.Tree.denote` type; `exists_prenex` needs to see its
      -- quantifiers, so present it at its (definitionally equal) formula.
      let parentProof ← if parent.clauseForm then pure parent.proof
        else mkExpectedTypeHint parent.proof parent.target
      let some prenexed ← BackendSkolemization.existsPrenex parentProof parent.step.existentialVariables
        | throwError "Skolemization `{step.name}` could not run `exists_prenex` on its parent"
      let some bindings := orderedSkolemBindings? prenexed.variables info
        | throwError "Skolemization `{step.name}` does not bijectively match the actual prenex-variable order {prenexed.variables}"
      return some (← withSkolemLets bindings 0 prenexed.proof derived typeAtoms termAtoms etoms
        symbols resumeWith)
  return none

/-- The rules that may have neither a source fact nor proof parents. -/
private def isParentlessRule (inference : Inference) : Bool :=
  inference.avatarDefinition?.isSome || inference.predicateDefinition?.isSome ||
    inference.choiceAxiom?.isSome || inference.functionalExtensionality?.isSome ||
    inference.rule == "theory_tautology_sat_conflict" ||
    inference.rule == "fool_exhaustiveness_axiom" || inference.rule == "fool_distinctness_axiom"

/-- Reconstruct one ordinary DAG node, whose symbols are all in scope, and
record its proof. -/
private def replayNode (context : ReplayContext) (state : ReplayState) (step : Step) :
    MetaM ReplayState := do
  let scope ← symbolScope context state
  let state := { state with scope? := some scope }
  let index := state.index
  let translatedStep ← translateStep context.typeAtoms state.termAtoms state.etoms step
  let target := translatedStep.formula
  let origin : String := match step.sourceFact?, step.inference? with
    | some fact, _ => s!"input `{fact}`"
    | none, some inference => s!"rule `{inference.rule}`"
    | none, none => "unannotated"
  trace[vampire.replay] "[{index}] replay {step.name}: {origin}; parents [{String.intercalate ", " (step.parents.map (·.name)).toList}]; leading universals {step.binders.size}"
  let parentProofs ← collectParentProofs context state step
  let sourceProof? : Option Expr ← match step.sourceFact? with
    | none => pure none
    | some fact =>
      let some proof := context.sourceProofs.get? fact
        | throwError "Vampire step `{step.name}` refers to unknown exported fact `{fact}`"
      pure (some proof)
  if parentProofs.isEmpty && sourceProof?.isNone && !step.inference?.any isParentlessRule then
    throwError "Vampire step `{step.name}` has neither a source fact nor proof parents"
  let satProof? ← translateSatProof context state step
  let input : RuleInput := {
    step, target, sourceProof?, symbols := state.symbols, satProof?
    clauseLiterals? := translatedStep.clauseLiterals?
    parents := parentProofs
    sourceFVars := context.allSources
    inhabitants := context.inhabitants
    avatarAtoms? := some scope.avatarAtoms
  }
  let proof ← reconstructNode scope input
  -- Present a formula-form proof at its decoded type.  Handlers may return a
  -- proof whose inferred type is only definitionally equal to the target
  -- (a `Clause.Tree.denote`, or a Skolem `Classical.choose` term in place of
  -- its let); later rules then see the proof-local symbols syntactically.
  -- Derived steps already carry exactly that hint.
  let storesClauseForm := Backend.storesClauseForm input
  let proof ← if ← (pure storesClauseForm <||> (do return (← inferType proof) == target)) then pure proof
    else pure (mkExpectedPropHint proof target)
  let replayed := state.replayed.insert step.name ⟨step, target, storesClauseForm,
    translatedStep.clauseLiterals?, proof⟩
  let finalProof? := if step.formula == .base .falseE then some proof else state.finalProof?
  pure { state with index := index + 1, replayed, finalProof? }

/-- Reconstruct the TPTP DAG in topological order. Ordinary nodes are replayed
in a loop; a node that needs a proof-local symbol first introduces its `let`
and continues the replay inside that scope. -/
private partial def replayStepsFrom (context : ReplayContext) (state : ReplayState) :
    MetaM Expr := do
  let mut state := state
  while h : state.index < context.steps.size do
    let step := context.steps[state.index]
    if let some proof ← introduceSymbols? context state step (replayStepsFrom context) then
      return proof
    state ← replayNode context state step
  let some finalProof := state.finalProof?
    | throwError "Vampire proof does not contain a decoded $false step"
  unless ← isDefEq (← inferType finalProof) (mkConst ``False) do
    throwError "the decoded Vampire $false step did not produce a Lean proof of False"
  -- All proof-local symbols are still in scope here. The local context starts
  -- empty in `buildLocalProof` and declares its signature without values, so
  -- its `let`s are exactly the replay's symbols, in introduction order. Close
  -- them in one abstraction pass rather than one pass per symbol.
  let lets := (← getLCtx).foldl (init := #[]) fun lets decl =>
    if decl.isLet then lets.push decl.toExpr else lets
  mkLetFVars lets finalProof

def replaySteps (steps : Array Step) (derived : Array DerivedSymbol)
    (flips : PolarityFlips)
    (allSources : Array FVarId) (sourceProofs : Std.HashMap String Expr)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr) (inhabitants : Array Expr := #[]) : MetaM Expr := do
  let cnfCache ← IO.mkRef {}
  let context : ReplayContext :=
    { steps, derived, allSources, sourceProofs, typeAtoms, inhabitants, cnfCache
      derivedByName := derived.foldl (fun map symbol => map.insertIfNew symbol.name symbol) {} }
  let state : ReplayState := { flips, termAtoms, etoms, symbols }
  replayStepsFrom context state

end VampireHammer.Replay.Internal

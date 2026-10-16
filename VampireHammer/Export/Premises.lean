import Auto.Tactic
import VampireHammer.Replay.Diagnostics
import VampireHammer.SourceNormalization
import VampireHammer.UnfoldingPlan
import VampireHammer.AttributeLemmas
import VampireHammer.Options
import VampireHammer.Export.ConstructorFacts
import VampireHammer.Export.InstanceDefinitions
import VampireHammer.Export.ProjectionDefinitions
import VampireHammer.Export.CoercionBridges
import VampireHammer.Export.LawInstances
import VampireHammer.Export.SiblingLemmas
import VampireHammer.Export.SuggestedLemmas
import VampireHammer.Export.DataWitnesses

/-!
Collect requested facts, local structure laws and attribute lemmas, and perform checked source
normalization before reification.
-/

namespace VampireHammer.Export.Internal

open Lean Meta Elab Tactic


/-- Instantiate projected laws whose binders depend on earlier binders (for
example `Category.assoc`) at the objects of the problem, so that they can pass
the quasi-monomorphic gate of monomorphization. Off by default: the
instantiated facts multiply the saturation work of monomorphization, which
starves the constant-instance specialization of premises (measured as
`Category.assoc` losing all of its specialized copies on
`CoverByImageStructure.fac_assoc`), and produced no recoveries on the
200-theorem sample. -/
register_option vampire.objectLaws : Bool := {
  defValue := false
  descr := "Instantiate object-quantified local laws at the problem's objects (experimental)"
}

/-- Label prefix of the facts projected from local typeclass instances. -/
def typeclassLawLabel : String := "typeclass law "

/-- Label prefix for optional laws stored in ordinary local records. -/
def structureLawLabel : String := "structure law "

/-- The required negated goal, preserved through checked source transformations. -/
def negatedGoalLabel : String := "vampire required negated goal"

/-- Maximum number of instantiations per projected law. -/
private def maxLawInstantiations : Nat := 3

/-- Maximum number of laws instantiated per collection. -/
private def maxObjectLawFacts : Nat := 12

/-- Maximum number of candidate objects per object binder. -/
private def maxLawObjects : Nat := 8

/-- `Quiver.Hom .. a b` as a pair of objects, if `type` is a hom. The
constant is compared by name so that no Mathlib import is needed. -/
private def homPair? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  let .const name _ := type.getAppFn | return none
  unless name.toString == "Quiver.Hom" do return none
  let args := type.getAppArgs
  if args.size < 2 then return none
  return some (args[args.size - 2]!, args[args.size - 1]!)

/-- The pairs of objects connected by a morphism of the problem: the types of
the local hypotheses that are `Quiver.Hom`s. -/
private def problemHomPairs : MetaM (Array (Expr × Expr)) := do
  let mut pairs : Array (Expr × Expr) := #[]
  for fvar in (← getLCtx).getFVars do
    let decl ← fvar.fvarId!.getDecl
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars (← inferType fvar)
    if type.hasMVar then continue
    if let some pair ← homPair? type then
      unless pair.1.hasMVar || pair.2.hasMVar do
        unless pairs.any fun (a, b) => a == pair.1 && b == pair.2 do
          pairs := pairs.push pair
  return pairs

/-- Whether some binder of `type` has a type mentioning an earlier binder:
the quasi-monomorphic gate of monomorphization rejects such facts. -/
private def binderDependsOnEarlier (type : Expr) : MetaM Bool := do
  forallTelescope type fun binders _ => do
    let mut ids : Array FVarId := #[]
    for binder in binders do
      let binderType ← instantiateMVars (← inferType binder)
      if binderType.hasAnyFVar ids.contains then return true
      ids := ids.push binder.fvarId!
    return false

/-- The leading binders of a law that later binders' types depend on, if they
form the whole leading prefix and no later binder depends on another later
one. Projected structure laws quantify over objects and then over morphisms
between them (`∀ X Y Z, (f : X ⟶ Y) (g : Y ⟶ Z), …`); the object prefix is
what the quasi-monomorphic gate rejects, so it is what has to be
instantiated. -/
private def objectPrefix? (binders : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut objectPrefix : Array Expr := #[]
  let mut i := 0
  while i < binders.size do
    let binder := binders[i]!
    let mentioned ← binders[i + 1:].anyM fun later => do
      let type ← instantiateMVars (← inferType later)
      return type.hasAnyFVar (· == binder.fvarId!)
    unless mentioned do break
    objectPrefix := objectPrefix.push binder
    i := i + 1
  if objectPrefix.isEmpty then return none
  for later in binders[i:] do
    let type ← instantiateMVars (← inferType later)
    if type.hasAnyFVar fun id =>
        (binders.any fun b => b.fvarId! == id) &&
          !(objectPrefix.any fun b => b.fvarId! == id) then
      return none
  return some objectPrefix

/-- Assignments of the object binders along the morphism graph of the problem:
every constrained pair of assigned objects must be connected by a morphism of
the problem. Bounded by `bound` assignments. -/
private partial def extendLawAssignment
    (constraints : Array (Nat × Nat)) (domains : Array (Array Expr))
    (pairs : Array (Expr × Expr)) (bound : Nat)
    (position : Nat) (assignment : Array Expr) (found : Array (Array Expr)) :
    MetaM (Array (Array Expr)) := do
  if found.size >= bound then return found
  if position == domains.size then return found.push assignment
  let mut result := found
  for candidate in domains[position]! do
    if result.size >= bound then break
    let mut ok := true
    for (ia, ib) in constraints do
      let valueOf (index : Nat) : Option Expr :=
        if index < position then assignment[index]?
        else if index == position then some candidate else none
      match valueOf ia, valueOf ib with
      | some va, some vb =>
        unless pairs.any fun (a, b) => a == va && b == vb do ok := false
      | _, _ => pure ()
      unless ok do break
    if ok then
      result ← extendLawAssignment constraints domains pairs bound (position + 1)
        (assignment.push candidate) result
  return result

/-- Instantiate the object prefix of a projected structure law at the
objects of the problem, along its morphisms; the data binders stay
quantified. The raw law cannot pass the quasi-monomorphic gate, and the
instantiated ones connect to the problem through its own morphisms. -/
private def instantiateLawObjects (proof type : Expr) (label : String) :
    MetaM (Array Auto.Lemma) := do
  let pairs ← problemHomPairs
  if pairs.isEmpty then return #[]
  forallTelescope type fun binders _ => do
    let some objectPrefix ← objectPrefix? binders | return #[]
    -- Morphism constraints from the data binders' hom types
    let mut constraints : Array (Nat × Nat) := #[]
    for binder in binders do
      if objectPrefix.contains binder then continue
      let binderType ← instantiateMVars (← inferType binder)
      let some (a, b) ← homPair? binderType | continue
      if let some ia := objectPrefix.findIdx? (· == a) then
        if let some ib := objectPrefix.findIdx? (· == b) then
          unless constraints.contains (ia, ib) do
            constraints := constraints.push (ia, ib)
    -- Every object binder is anchored by some morphism of the problem
    let mut anchored : Array Nat := #[]
    for (ia, ib) in constraints do
      unless anchored.contains ia do anchored := anchored.push ia
      unless anchored.contains ib do anchored := anchored.push ib
    if anchored.size < objectPrefix.size then return #[]
    -- Candidate objects per object binder
    let mut domains : Array (Array Expr) := #[]
    for binder in objectPrefix do
      let binderType ← instantiateMVars (← inferType binder)
      let mut domain : Array Expr := #[]
      for fvar in (← getLCtx).getFVars do
        if binders.contains fvar then continue
        let decl ← fvar.fvarId!.getDecl
        if decl.isImplementationDetail then continue
        let fvarType ← instantiateMVars (← inferType fvar)
        if fvarType.hasMVar then continue
        if ← isDefEq binderType fvarType then
          domain := domain.push fvar
          if domain.size >= maxLawObjects then break
      if domain.isEmpty then return #[]
      domains := domains.push domain
    -- Assignments along the morphism graph of the problem
    let assignments ← extendLawAssignment constraints domains pairs maxLawInstantiations
      0 #[] #[]
    let mut facts : Array Auto.Lemma := #[]
    for assignment in assignments do
      let instantiated := mkAppN proof assignment
      let type ← instantiateMVars (← inferType instantiated)
      unless type.hasMVar do
        facts := facts.push ⟨⟨← mkExpectedTypeHint instantiated type, type, .leaf label⟩, #[]⟩
    return facts

/-- Project proposition fields from the actual local structure value, including
inherited fields. This handles both class instances and ordinary records such
as functors. Data fields are ignored; no global instance search or mathematical
lemma names are needed. -/
private def collectLocalStructureLaws (exclude? : Option Name) : MetaM (Array Auto.Lemma) := do
  let env ← getEnv
  let mut laws := #[]
  for fVarId in (← getLCtx).getFVarIds do
    let decl ← fVarId.getDecl
    if decl.isAuxDecl then continue
    let structureType ← instantiateMVars decl.type
    let className? ← Meta.isClass? structureType
    let structureName ← match className? with
      | some name => pure name
      | none =>
        -- Local proof hypotheses already belong to the requested fact set.
        -- Projecting their logical fields would also bypass explicit hints.
        if ← isProp structureType then continue
        let .const name _ := (← whnf structureType).getAppFn | continue
        pure name
    -- Nonempty and other inductives do not have structure projection metadata.
    if (Lean.getStructureInfo? env structureName).isNone then continue
    let label := if className?.isSome then typeclassLawLabel else structureLawLabel
    trace[vampire] "Extracting proposition-valued fields from local {structureName} value {decl.userName}"
    -- Raw laws whose binders depend on earlier binders cannot pass the
    -- quasi-monomorphic gate; only their object-instantiated versions can.
    let mut instantiatedLaws := 0
    for fieldName in Lean.getStructureFieldsFlattened env structureName true do
      let saved ← saveState
      try
        let proof ← Meta.mkProjection (mkFVar fVarId) fieldName
        -- When reproving a generated projection theorem, access the instance
        -- field with the kernel's primitive projection instead of referring
        -- to that same theorem as a premise.
        let proof := Id.run do
          let .const name _ := proof.getAppFn | return proof
          unless exclude? == some name do return proof
          let some info := env.getProjectionFnInfo? name | return proof
          let some projectedStructure := env.getProjectionStructureName? name | return proof
          let args := proof.getAppArgs
          if info.numParams >= args.size then return proof
          return mkAppN (.proj projectedStructure info.i args[info.numParams]!)
            (args.extract (info.numParams + 1) args.size)
        let type ← instantiateMVars (← inferType proof)
        if ← Meta.isProp type then
          let fieldLabel := s!"{label}{fieldName} from {decl.userName} : {structureName}"
          -- The raw law is always kept: even when the export gate drops it,
          -- its quantified form still drives the constant-instance
          -- specialization of other facts (premises such as `Category.assoc`)
          -- during monomorphization.
          laws := laws.push ⟨⟨proof, type, .leaf fieldLabel⟩, #[]⟩
          let objectLaws := vampire.objectLaws.get (← getOptions)
          if objectLaws && (← binderDependsOnEarlier type) then
            -- The raw law cannot pass the export gate itself, so also
            -- instantiate its object binders at the problem's own objects
            -- along its morphisms, keeping the data binders quantified.
            let saved ← saveState
            let instantiated ←
              try instantiateLawObjects proof type
                    s!"{label}{fieldName} at objects from {decl.userName} : {structureName}"
              catch _ =>
                saved.restore
                pure #[]
            for fact in instantiated do
              if instantiatedLaws >= maxObjectLawFacts then break
              laws := laws.push fact
              instantiatedLaws := instantiatedLaws + 1
      catch _ =>
        saved.restore
        trace[vampire] "Could not inspect field {fieldName} of local structure {structureName}"
  trace[vampire] "Collected {laws.size} proposition-valued local structure laws"
  pure laws

/-- Lower variable-indexed numeral notation to the ordinary `Nat.cast`
operation when Lean can justify that reduction by definitional equality.

lean-auto gives numeric literals special Lam syntax.  Its reifier deliberately
expects the index of `OfNat.ofNat` to be a literal, so a term such as
`OfNat.ofNat n : R` (where `n : Nat` is a variable) stops reification before
it can be treated as an ordinary first-order operation.  For the usual
algebraic instances, however, that notation is definitionally the canonical
map `Nat.cast : Nat → R`.  Once exposed, `Nat.cast` is a perfectly ordinary
opaque first-order function of type `Nat → R`.

This is a *definitional* source normalization, not a rewrite by a theorem and
not a simplifier pass.  We build the `Nat.cast` candidate using the available
`NatCast R` instance and keep it only if Lean's kernel says it is definitionally
equal to the original `OfNat` expression.  Consequently custom `OfNat R n`
instances that are not induced by a `NatCast R` are left untouched; their
meaning cannot in general be represented by one uniform `Nat → R` function.
-/
private def lowerDefeqNatCasts (type : Expr) : MetaM Expr :=
  -- `Meta.transform` opens binders before invoking `post`, so `inferType` and
  -- instance search below also work for numeral notation under quantifiers.
  Meta.transform type (post := fun expression => do
    let function := expression.getAppFn
    let arguments := expression.getAppArgs
    unless function.isConstOf ``OfNat.ofNat && arguments.size == 3 do
      return .done expression
    -- Auto already recognizes literal indices. Replacing them can introduce
    -- Nat.cast instances after its constant-instance catalogue was collected.
    if let .lit (.natVal _) := arguments[1]! then return .done expression
    try
      let resultType ← inferType expression
      -- `resultType : Type level`, so the universe argument of `Nat.cast` is
      -- `level` (not the successor level of the type of `resultType`).  Its
      -- instance argument is built explicitly, rather than with `mkAppM`, so
      -- instance synthesis already knows the target type `resultType`.
      let .sort (.succ level) ← inferType resultType
        | return .done expression
      let natCastType ← mkAppM ``NatCast #[resultType]
      let natCastInstance ← synthInstance natCastType
      let cast := mkApp3 (mkConst ``Nat.cast [level]) resultType natCastInstance arguments[1]!
      if ← isDefEq expression cast then
        trace[vampire] "Lowered variable-indexed OfNat notation to Nat.cast"
        return .done cast
      else
        return .done expression
    catch _ =>
      -- Most `OfNat` instances do not provide a uniform `NatCast`.  They must
      -- not be guessed at: retaining the original term lets the normal
      -- lean-auto diagnostics explain that the source is outside this TF0
      -- lowering fragment.
      return .done expression)

/-- Apply the definitionally checked numeral lowering to the proposition type
of one source fact.  The proof object itself is retained: Lean accepts it at
the new type because the transformation above only uses definitional equality.
-/
private def lowerDefeqNatCastsInLemma (lemma : Auto.Lemma) : MetaM Auto.Lemma := do
  let ⟨fact, parameters⟩ := lemma
  let type ← lowerDefeqNatCasts fact.type
  pure ⟨{ fact with type }, parameters⟩

/-- Collect a bare proof as its complete polymorphic constant, without
inserting implicit/default arguments. In particular an `autoParam` tactic
must not run while elaborating an unconstrained premise. Local names, applied
terms and bundled definitions keep their ordinary elaboration behavior. -/
private def explicitProofHints (hints : TSyntax ``Auto.hints) :
    TacticM (TSyntax ``Auto.hints) := do
  let `(Auto.hints| [ $[$elems],* ]) := hints | return hints
  let mut explicit := #[]
  for elem in elems do
    let `(Auto.hintelem| $term:term) := elem | explicit := explicit.push elem; continue
    unless term.raw.isIdent do explicit := explicit.push elem; continue
    if ((← getLCtx).findFromUserName? term.raw.getId).isSome then
      explicit := explicit.push elem
      continue
    let name? ← try some <$> resolveGlobalConstNoOverload term.raw catch _ => pure none
    let some name := name? | explicit := explicit.push elem; continue
    let some info := (← getEnv).find? name | explicit := explicit.push elem; continue
    unless ← isProp info.type do explicit := explicit.push elem; continue
    let constant : Term := ⟨mkIdent name⟩
    let term ← `(term| @$constant)
    explicit := explicit.push (← `(Auto.hintelem| $term:term))
  `(Auto.hints| [ $explicit,* ])

/-- lean-auto rejects the whole call when one explicit hint states inhabitation
(`Nonempty α`, `Inhabited α`, possibly under binders) or is not a proposition,
e.g. a premise list taken from a library proof. Turn the former into
inhabitation facts, `∀ xs, α` proved by `Classical.choice`/`Inhabited.default`,
and drop the latter: omitting a premise from a refutation is sound. A closed
non-proposition, such as a bundled map `ENNReal.toRealHom`, is returned with
its label for `CoercionBridges.hintBridges`. Terms that fail to elaborate stay
in the hints, so lean-auto reports their error. Every non-proposition, also
one with arguments such as `Equiv.ulift`, is a witness for `DataWitnesses`. -/
private def separateHints (hints : TSyntax ``Auto.hints) :
    TacticM (TSyntax ``Auto.hints × Array Auto.Lemma × Array (Expr × String × Array Name) ×
      Array DataWitnesses.Witness) := do
  let `(Auto.hints| [ $[$elems],* ]) := hints | return (hints, #[], #[], #[])
  let mut kept := #[]
  let mut inhabitants := #[]
  let mut values := #[]
  let mut witnesses := #[]
  for elem in elems do
    let `(Auto.hintelem| $term:term) := elem | kept := kept.push elem; continue
    let lemma? ← try
      some <$> withNewMCtxDepth (Auto.Prep.elabLemma term (.leaf s!"❰{term}❱"))
    catch _ => pure none
    let some ⟨⟨proof, type, deriv⟩, params⟩ := lemma? | kept := kept.push elem; continue
    if ← Auto.Prep.isNonemptyInhabited type then
      let inhabitant? ← forallTelescope type fun xs body => do
        let body ← whnfR body
        let value? := match body.getAppFn, body.getAppArgs with
          | .const ``Nonempty [u], #[α] => some (α, mkApp2 (.const ``Classical.choice [u]) α (mkAppN proof xs))
          | .const ``Inhabited [u], #[α] => some (α, mkApp2 (.const ``Inhabited.default [u]) α (mkAppN proof xs))
          | _, _ => none
        let some (α, value) := value? | return none
        return some (← mkLambdaFVars xs value, ← mkForallFVars xs α)
      if let some (proof, type) := inhabitant? then
        inhabitants := inhabitants.push ⟨⟨proof, type, deriv⟩, params⟩
      else
        trace[vampire] "Dropping inhabitation hint {term} with unrecognized type {type}"
    else if ← isProp type then
      kept := kept.push elem
    else
      unless type.isForall do values := values.push (proof, s!"❰{term}❱", params)
      witnesses := witnesses.push { value := proof, type, params, label := s!"❰{term}❱" }
      trace[vampire] "Not passing hint {term} as a fact: its type {type} is not a proposition"
  return (← `(Auto.hints| [ $kept,* ]), inhabitants, values, witnesses)

/-- Collect lean-auto's usual facts and supplement them with laws contained in
local structure values, including the theorem's typeclass parameters.  Both `vampire`
and `vampire_export` call this helper so the inspected TPTP problem is exactly
the problem reconstructed by the prover path. -/
def collectFactsWithTypeclassLaws
    (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord))
    (binders : Array FVarId) (negHyp : FVarId) (exposedDefinitions : Array Name := #[]) :
    TacticM (Array Auto.Lemma × Array Auto.Lemma) := do
  let nestedDefinitions ← liftMetaM <|
    SourceNormalization.collectLogicalDefinitions (← negHyp.getType)
  let hints ← explicitProofHints hints
  let (hints, hintInhabitants, hintValues, witnesses) ← separateHints hints
  let (lemmas, inhs) ← Auto.collectAllLemmas hints uords (binders.push negHyp)
  -- Auto labels the negated goal like any local hypothesis. Keep it outside
  -- the optional-local prefix so the subset retry cannot omit the target.
  let lemmas := lemmas.map fun lemma =>
    if lemma.proof == mkFVar negHyp then
      { lemma with deriv := .leaf negatedGoalLabel }
    else lemma
  let inhs := inhs ++ hintInhabitants
  let lemmas ← liftMetaM <| lemmas.mapM lowerDefeqNatCastsInLemma
  -- Bridges match the functions as the user wrote them; normalization can
  -- expand `∏ i ∈ s, f i` into `Multiset`/`Quot` internals.
  let sourceLemmas := lemmas
  -- Relevance comes from the requested source problem. Exploring every
  -- universally quantified class law would pull in unrelated attributed facts.
  let attributeLemmas ← liftMetaM <| AttributeLemmas.collect lemmas (← Term.getDeclName?)
  -- Siblings anchor on the same requested facts; their selection is disabled by
  -- default and measured independently of the attribute lemmas.
  let siblingLemmas ← liftMetaM <| SiblingLemmas.collect lemmas (← Term.getDeclName?)
  -- Library suggestions rank environment theorems by the symbols of the goal
  -- and local hypotheses; disabled by default.
  let declName? ← Term.getDeclName?
  let suggestedLemmas ← liftMetaM do
    let .app (.const ``Not _) target ← instantiateMVars (← negHyp.getType) | pure #[]
    SuggestedLemmas.collect lemmas target declName?
  -- Data arguments that monomorphization cannot choose, such as the
  -- equivalence of `Equiv.isEmpty`, from non-proposition hints and local data.
  let witnessFacts ← liftMetaM do
    let premises := lemmas.filter fun lemma => match lemma.deriv with
      | .leaf label => label.startsWith "❰"
      | _ => false
    let propositions ← (← getLCtx).getFVars.filterMapM fun x => do
      let type ← instantiateMVars (← inferType x)
      return if ← isProp type then some type else none
    DataWitnesses.instantiate premises witnesses propositions
  let requestedCount := lemmas.size
  let structureLaws ← liftMetaM <|
    (← collectLocalStructureLaws declName?).mapM lowerDefeqNatCastsInLemma
  let lemmas ← liftMetaM <|
    (lemmas ++ structureLaws ++ attributeLemmas ++ siblingLemmas ++ suggestedLemmas ++
      witnessFacts).mapM SourceNormalization.normalizeLemma
  -- Premises instantiated at witnesses count as requested: their bundled
  -- values need the same projection and constructor equations.
  let requested := lemmas.extract 0 requestedCount ++
    lemmas.extract (lemmas.size - witnessFacts.size) lemmas.size
  -- Logically defined local operations keep their symbol; the definition is
  -- an extra fact. Its constructors (`Low`, `High`) also need their laws.
  let instanceDefinitions ← liftMetaM <|
    (← InstanceDefinitions.collect requested).mapM SourceNormalization.normalizeLemma
  -- `(e.symm).toFun y` and `e.invFun y` are one term for Lean but two symbols
  -- for the prover; the defining equation of the projection relates them.
  let projectionDefinitions ← liftMetaM <|
    (← ProjectionDefinitions.collect requested).mapM SourceNormalization.normalizeLemma
  let constructorLaws ← liftMetaM <| ConstructorFacts.collect (requested ++ instanceDefinitions)
  -- Law-instance facts pass through the same checked normalization as the
  -- structure laws: both are projected theorems rather than source hypotheses.
  -- Besides the requested facts, the fields of the caller's own local
  -- instances anchor the search: an operation such as `Nat` addition can occur
  -- inside an instance field (`natCast_succ`) without occurring in any
  -- hypothesis or goal.  Anchoring on those fields keeps every operation of
  -- the problem context covered by its `Std` laws without a built-in theory.
  let anchoredFacts := lemmas.extract 0 (requestedCount + structureLaws.size)
  -- The structure laws remain in the problem as axioms, so a law they already
  -- states (the `one_mul` and `mul_one` fields of a local `MulOneClass`, say)
  -- needs no synthesized copy.  The requested facts are deliberately not in
  -- that baseline: the goal is negated rather than kept, so even a law it
  -- states must still be exported as an axiom.
  let statedLaws := (lemmas.extract requestedCount (requestedCount + structureLaws.size)).map (·.type)
  let lawInstances ← liftMetaM <| LawInstances.collect anchoredFacts statedLaws
  let lawInstances ← liftMetaM <| lawInstances.mapM SourceNormalization.normalizeLemma
  -- Generic laws such as `map_prod (f : F)` need a coercion `⇑f` of the
  -- problem; relate bundled maps to the plain functions of the goal.
  let coercionBridges ← liftMetaM do
    let bridges := (← CoercionBridges.hintBridges hintValues sourceLemmas) ++
      (← CoercionBridges.collect sourceLemmas)
    bridges.mapM SourceNormalization.normalizeLemma
  let lemmas := lemmas ++ instanceDefinitions ++ projectionDefinitions ++ coercionBridges ++
    constructorLaws ++ lawInstances
  -- `Bool` is an uninterpreted sort for the prover; lean-auto's `boolFacts`
  -- state its constants but not that they are its only values.
  let mentionsBool := lemmas.any fun lemma => (lemma.type.find? (·.isConstOf ``Bool)).isSome
  let exhaustive := mkConst ``Bool.eq_false_or_eq_true
  let exhaustiveType ← liftMetaM <| inferType exhaustive
  let lemmas := if mentionsBool then
      lemmas.push ⟨⟨exhaustive, exhaustiveType, .leaf "Bool.eq_false_or_eq_true"⟩, #[]⟩
    else lemmas
  -- `decide p` that lean-auto does not rewrite to `ofProp` is otherwise an
  -- unrelated Boolean function of `p`.
  let mentionsDecide := lemmas.any fun lemma =>
    (lemma.type.find? (·.isConstOf ``Decidable.decide)).isSome
  let decideSpec := mkConst ``decide_eq_true_eq
  let decideSpecType ← liftMetaM <| inferType decideSpec
  let lemmas := if mentionsDecide then
      lemmas.push ⟨⟨decideSpec, decideSpecType, .leaf "decide_eq_true_eq"⟩, #[]⟩
    else lemmas
  if vampire.unfoldingPlan.get (← getOptions) then
    -- One decision per definition for the whole problem; see `UnfoldingPlan`.
    let requested := exposedDefinitions ++ nestedDefinitions.filter (!exposedDefinitions.contains ·)
    let lemmas ← liftMetaM do
      let facts := lemmas.map fun lemma => (lemma.type, UnfoldingPlan.side lemma.deriv)
      UnfoldingPlan.applyToLemmas (← UnfoldingPlan.plan facts requested) lemmas
    return (lemmas, inhs)
  let mut exposedDefinitions := exposedDefinitions
  for name in nestedDefinitions do
    unless exposedDefinitions.contains name do exposedDefinitions := exposedDefinitions.push name
  if exposedDefinitions.isEmpty then return (lemmas, inhs)
  trace[vampire.unfold] "Aligning selected facts with goal definitions: {exposedDefinitions}"
  -- Preserve the interface facts and add definitionally equal expanded
  -- copies only for the definitions opened in the goal. The original proof
  -- objects justify every copy; this introduces neither axioms nor hints.
  let unfolds? ← liftMetaM do
    let saved ← saveState
    try
      let unfolds ← exposedDefinitions.mapM Auto.Prep.getConstUnfoldInfo
      return some (← Auto.Prep.topoSortUnfolds unfolds)
    catch error =>
      saved.restore
      trace[vampire.unfold] "Definition alignment declined: {error.toMessageData}"
      return none
  let some unfolds := unfolds? | return (lemmas, inhs)
  let mut expanded := #[]
  for lemma in lemmas do
    unless (lemma.type.find? fun expression =>
        expression.isConst && exposedDefinitions.contains expression.constName!).isSome do
      continue
    let copy ← liftMetaM do
      SourceNormalization.normalizeLemma (← Auto.unfoldConstAndPreprocessLemma unfolds lemma)
    if copy.type == lemma.type || copy.type.sizeWithoutSharing > lemma.type.sizeWithoutSharing + 4096 then
      continue
    unless lemmas.any (·.type == copy.type) || expanded.any (·.type == copy.type) do
      expanded := expanded.push copy
  trace[vampire.unfold] "Added {expanded.size} definitionally expanded source facts"
  pure (lemmas ++ expanded, inhs)

end VampireHammer.Export.Internal

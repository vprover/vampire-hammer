import VampireHammer.Replay.Translation
import VampireHammer.Backend

/-!
Continuation-based bindings for proof-local Skolem witnesses, AVATAR definitions, named
predicates, and polarity flips.

Each helper introduces its symbol with `withLetDecl` and returns its continuation's
result unchanged. The continuation must close the `let` itself: the replay loop
abstracts all proof-local `let`s with one `mkLetFVars` once the whole DAG is
replayed, instead of one pass over the remaining proof per symbol.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend

/-! ### Sequential proof-local Skolem lets

The proof DAG is replayed in Vampire's topological order. At a `skolemize`
node, its cited parent is therefore already a real Lean proof. We can put the
fresh symbols in nested `let`s *at that point*, exactly like the generated
paper proofs do. This matters for an `ennf_transformation → skolemize` pair:
there is no exported source hypothesis of the prenexed parent to use during a
global prepass.
-/

private def installDerivedSymbol (symbol : DerivedSymbol) (value : Expr)
    (termAtoms etoms : Std.HashMap Nat Expr) :
    Std.HashMap Nat Expr × Std.HashMap Nat Expr :=
  match symbol.term with
  | .atom atom => (termAtoms.insert atom value, etoms)
  | .etom etom => (termAtoms, etoms.insert etom value)
  | _ => (termAtoms, etoms)

/-- Abstract the certified dependency subset, rejecting an omitted variable
that occurs in the witness value or its type. All parent binders are still
opened when interpreting the selected literal. -/
private def abstractWitnessDependencies (args : Array Expr) (indices : Array Nat)
    (value : Expr) : MetaM Expr := do
  let type ← inferType value
  for (argument, index) in args.zipIdx do
    if !indices.contains index &&
        (value.containsFVar argument.fvarId! || type.containsFVar argument.fvarId!) then
      throwError "witness certificate omits a required parent dependency"
  mkLambdaFVars (indices.map (args[·]!)) value

/-- Generalize dependency terms in order. The abstracted value must be closed
with respect to the parent binders `args`. -/
private def abstractWitnessTerms (args terms : Array Expr) (value : Expr) : MetaM Expr := do
  let rec go (index : Nat) (body : Expr) (fvars : Array Expr) : MetaM Expr := do
    if h : index < terms.size then
      let term := terms[index]
      withLocalDeclD (Name.mkSimple s!"dependency{index}") (← inferType term) fun fresh => do
        let abstracted ← kabstract body term
        go (index + 1) (abstracted.instantiate1 fresh) (fvars.push fresh)
    else
      let type ← inferType body
      for argument in args do
        if body.containsFVar argument.fvarId! || type.containsFVar argument.fvarId! then
          throwError "witness dependency terms do not cover parent variable {argument}"
      mkLambdaFVars fvars body
  go 0 value #[]

/-- Bind a certified difference witness to its classical interpretation,
abstracting the selected parent binders in their recorded dependency order. The value
does not depend on the parent proof, so local parent-to-child lemmas remain
independent of the previously reconstructed DAG. -/
def withDifferenceWitnessLet (info : NegativeExtensionalityInfo) (parent : StepProof)
    (derived : Std.HashMap String DerivedSymbol) (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "difference witness `{info.symbol}` has no checked declaration"
  unless symbol.kind == .differenceWitness && !symbols.contains symbol.name do
    throwError "difference witness `{info.symbol}` is not fresh"
  let some dependencies := witnessDependencyIndices? (parent.step.binders.map (·.name)) info.dependencies
    | throwError "difference witness `{info.symbol}` has incorrect dependencies"
  let some literals := parent.clauseLiterals?
    | throwError "difference witness requires a clause parent"
  let some selected := literals[info.literal.index]?
    | throwError "difference witness literal index is out of range"
  let value ← forallBoundedTelescope parent.target (some parent.step.binders.size) fun args _ => do
    unless args.size == parent.step.binders.size do throwError "difference witness binder count mismatch"
    let selected ← Core.betaReduce (selected.instantiateRev args)
    let some equation := selected.not? | throwError "difference witness requires a disequality"
    let some (_, left, right) := equation.eq? | throwError "difference witness requires equality operands"
    let type ← whnf (← inferType left)
    let .forallE _ _ range _ := type
      | throwError "difference witness requires function operands"
    if range.hasLooseBVars then throwError "dependent extensionality is unsupported"
    let value ← mkAppM ``differenceWitness #[left, right]
    abstractWitnessDependencies args dependencies value
  let expected ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  unless ← isDefEq (← inferType value) expected do
    throwError "difference witness `{info.symbol}` has an incorrect declared type"
  trace[vampire.replay] "difference witness let {symbol.name} : {expected} := {value}"
  withLetDecl (Name.mkSimple symbol.name) expected value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

/-- Bind a certified fresh choice operator to its classical interpretation. -/
def withChoiceOperatorLet (info : ChoiceAxiomInfo) (derived : Std.HashMap String DerivedSymbol)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr) (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "choice operator `{info.symbol}` has no checked declaration"
  unless info.introduce && symbol.kind == .choiceOperator && !symbols.contains symbol.name do
    throwError "choice operator `{info.symbol}` is not a fresh interpreted operator"
  let type ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  let some value ← higherOrderChoiceValue type
    | throwError "choice operator `{info.symbol}` has an unsupported type or missing inhabitant"
  trace[vampire.replay] "choice operator let {symbol.name} : {type} := {value}"
  withLetDecl (Name.mkSimple symbol.name) type value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

def withDifferenceOperatorLet (info : FunctionalExtensionalityInfo) (derived : Std.HashMap String DerivedSymbol)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr) (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "difference operator `{info.symbol}` has no checked declaration"
  unless info.introduce && symbol.kind == .differenceOperator && !symbols.contains symbol.name do
    throwError "difference operator `{info.symbol}` is not a fresh interpreted operator"
  let type ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  let some value ← higherOrderDifferenceValue type
    | throwError "difference operator `{info.symbol}` has an unsupported type or missing inhabitant"
  trace[vampire.replay] "difference operator let {symbol.name} : {type} := {value}"
  withLetDecl (Name.mkSimple symbol.name) type value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

/-- Bind a quantified proxy witness independently of the parent proof. -/
def withQuantifierWitnessLet (info : QuantifierWitnessInfo) (parent : StepProof)
    (derived : Std.HashMap String DerivedSymbol) (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "quantifier witness `{info.symbol}` has no checked declaration"
  unless symbol.kind == .quantifierWitness && !symbols.contains symbol.name do
    throwError "quantifier witness `{info.symbol}` has incorrect freshness"
  let names := parent.step.binders.map (·.name)
  let some dependencies := witnessDependencyIndices? names info.dependencies
    | throwError "quantifier witness `{info.symbol}` has incorrect dependencies"
  let some literals := parent.clauseLiterals? | throwError "quantifier witness requires a clause"
  let some selected := literals[info.literal.index]? | throwError "quantifier witness index out of range"
  let value ← forallBoundedTelescope parent.target (some parent.step.binders.size) fun args _ => do
    unless args.size == parent.step.binders.size do throwError "quantifier witness binder count mismatch"
    let selected ← Core.betaReduce (selected.instantiateRev args)
    let some (_, predicate) ← higherOrderExistentialCondition selected
      | throwError "quantifier witness requires an existential or negated universal"
    let witness ← mkAppM ``quantifierWitness #[predicate]
    if info.dependencyTerms.isEmpty then
      return ← abstractWitnessDependencies args dependencies witness
    -- Term dependencies: generalize each displayed term to a fresh binder.
    -- No parent variable may remain, so `sK t…` denotes exactly this witness.
    let mut terms := #[]
    for raw in info.dependencyTerms do
      let some term ← Internal.materializeMetadataTerm raw symbols (names.zip args)
        | throwError "quantifier witness `{info.symbol}` has an invalid dependency term"
      terms := terms.push term
    abstractWitnessTerms args terms witness
  let expected ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  unless ← isDefEq (← inferType value) expected do
    throwError "quantifier witness `{info.symbol}` has an incorrect declared type"
  trace[vampire.replay] "quantifier witness let {symbol.name} : {expected} := {value}"
  withLetDecl (Name.mkSimple symbol.name) expected value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

/-- Introduce every fresh symbol in one multi-variable `skolemize` step.

`bindings` has already been reordered with the actual prenex witness order. The
recursive call deliberately uses the residual `choose_spec` proof, hence the
second `let` is selected from the formula after the first choice, rather than
from the original parent again. -/
partial def withSkolemLets (bindings : Array SkolemBinding) (index : Nat)
    (prenexed : Expr) (derived : Std.HashMap String DerivedSymbol)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  if h : index < bindings.size then
    let binding := bindings[index]
    let some symbol := derived.get? binding.symbol
      | throwError "Skolem `{binding.symbol}` has no checked TFF declaration"
    unless symbol.kind == .skolem do
      throwError "fresh symbol `{binding.symbol}` is not declared as a Skolem"
    if symbols.contains binding.symbol then
      throwError "Skolem `{binding.symbol}` was introduced twice"
    let expectedType ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
    trace[vampire.replay] "Skolem `{binding.symbol}` unpacking prenex remainder {← inferType prenexed}"
    let some (value, residual) ← BackendSkolemization.chooseWitness prenexed
      | throwError "Skolem `{binding.symbol}` has no remaining existential witness after `exists_prenex`"
    unless ← isDefEq (← inferType value) expectedType do
      throwError "Skolem `{binding.symbol}` has TFF type {expectedType}, but `exists_prenex` produced {← inferType value}"
    trace[vampire.replay] "Skolem let {binding.symbol} for original variable {binding.existentialVariable}: {expectedType}"
    withLetDecl (Name.mkSimple binding.symbol) expectedType value fun symbolFVar => do
      let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
      withSkolemLets bindings (index + 1) residual derived typeAtoms termAtoms etoms
        (symbols.insert binding.symbol symbolFVar) k
  else
    k termAtoms etoms symbols

/-- Return the bindings in the order in which `exists_prenex` exposes their
witnesses. Occurrence matching supplies original variable names; the certificate
supplies their fresh symbols. Requiring a bijection prevents a malformed
certificate from changing a witness association by omission. -/
def orderedSkolemBindings? (variables : Array String) (info : SkolemizationInfo) :
    Option (Array SkolemBinding) := do
  guard (variables.size == info.bindings.size)
  guard (variables.toList.eraseDups.length == variables.size)
  variables.mapM fun variableName =>
    info.bindings.find? (·.existentialVariable == variableName)

/-- Read the component side of `spl ↔ component` before the fresh `spl` is
introduced into the local term map. The body may use symbols created by earlier
proof-DAG nodes, including a preceding proof-local Skolem function. -/
private def avatarDefinitionBody? (symbol : LamTerm) : LamTerm → Option LamTerm
  | .app _ (.app _ (.base .iff) left) right =>
    if left == symbol && right != symbol then some right
    else if right == symbol && left != symbol then some left
    else none
  | _ => none

/-- Introduce one AVATAR component at its definition node. Keeping this beside
the Skolem path makes every proof-local symbol sequential: no definition is
translated before the symbols on which its value depends are in scope. -/
def withAvatarDefinitionLet (step : Step) (info : AvatarDefinitionInfo)
    (derived : Std.HashMap String DerivedSymbol) (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "AVATAR component `{info.symbol}` has no derived-symbol entry"
  unless symbol.kind == .avatarDefinition do
    throwError "fresh symbol `{info.symbol}` is not declared as an AVATAR component"
  if symbols.contains symbol.name then
    throwError "AVATAR component `{symbol.name}` was introduced twice"
  unless step.binders.isEmpty do
    throwError "AVATAR definition `{step.name}` unexpectedly has binders"
  let some body := avatarDefinitionBody? symbol.term step.formula
    | throwError "AVATAR definition `{step.name}` is not `{symbol.name} ↔ component`"
  let expectedType ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  let value ← translateLocal typeAtoms termAtoms etoms body
  unless ← isDefEq (← inferType value) expectedType do
    throwError "AVATAR definition `{step.name}` has a non-propositional component"
  trace[vampire.replay] "AVATAR let {symbol.name} : {expectedType} := {value}"
  withLetDecl (Name.mkSimple symbol.name) expectedType value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

/-- Split a `LamTerm` application into its head and arguments, in order. -/
private def splitLamApp : LamTerm → LamTerm × List LamTerm
  | .app _ fn arg =>
    let (head, args) := splitLamApp fn
    (head, args ++ [arg])
  | term => (term, [])

/-- Move the body of a naming definition below fresh lambdas, one per symbol
argument.  `args` lists the outer de Bruijn index passed as each argument; the
body may mention no other outer variable, so a closed function results. -/
private def abstractNamedBody (args : Array Nat) : Nat → LamTerm → Option LamTerm
  | depth, .bvar index =>
    if index < depth then some (.bvar index)
    else do
      let position ← args.findIdx? (· == index - depth)
      pure (.bvar (depth + args.size - 1 - position))
  | depth, .lam sort body => .lam sort <$> abstractNamedBody args (depth + 1) body
  | depth, .app sort fn arg =>
    .app sort <$> abstractNamedBody args depth fn <*> abstractNamedBody args depth arg
  | _, term => some term

/-- Read the value of `sP` from a formula-naming definition
`∀ x̄, φ x̄ ∨ ¬ sP x̄`.  Choosing `sP := fun x̄ => φ x̄` makes the definition hold;
the same choice also works for an `↔` definition, and the positive spelling
`ψ x̄ ∨ sP x̄` uses `fun x̄ => ¬ ψ x̄`.

The other fresh-symbol definitions use the same reading:
* general splitting's `∀ x̄, (∀ y, M) ↔ ¬ sP x̄` gives `fun x̄ => ¬ ∀ y, M`;
* a function definition `sF x̄ = t` (either side) gives `fun x̄ => t`;
* an equality proxy `sQ x y ↔ x = y` is an ordinary `↔` definition;
* an inequality-splitting name `¬ sP t`, for a ground `t`, gives
  `fun x => x ≠ t`: the split literal `s ≠ t` becomes `sP s`. -/
private def predicateDefinitionValue? (symbol : LamTerm) (sort : LamSort)
    (binders : Nat) (formula : LamTerm) : Option LamTerm := do
  let body ← stripLeadingForalls binders formula
  let isSymbolApp := fun (term : LamTerm) => (splitLamApp term).1 == symbol
  if let .app _ (.base .not) inner := body then
    let (head, arguments) := splitLamApp inner
    if head == symbol then
      if let [ground] := arguments then
        if ground.maxLooseBVarSucc == 0 then
          let (argSorts, _) := signature sort
          let [argSort] := argSorts | none
          return .lam argSort (.mkNot (.mkEq argSort (.bvar 0) ground))
  let (literal, named) ← match body with
    | .app _ (.app _ (.base .iff) left) right =>
      if isSymbolApp left then some (left, right)
      else if isSymbolApp right then some (right, left)
      else match left, right with
        | _, .app _ (.base .not) inner =>
          if isSymbolApp inner then some (inner, .mkNot left) else none
        | .app _ (.base .not) inner, _ =>
          if isSymbolApp inner then some (inner, .mkNot right) else none
        | _, _ => none
    | .app _ (.app _ (.base (.eq _)) left) right =>
      if isSymbolApp left then some (left, right)
      else if isSymbolApp right then some (right, left)
      else none
    | _ =>
      let literals := flattenOr body
      let index ← literals.findIdx? fun literal =>
        isSymbolApp literal || match literal with
          | .app _ (.base .not) inner => isSymbolApp inner
          | _ => false
      let rest := (rightAssociate? .mkOr (literals.eraseIdx index)).getD (.base .falseE)
      match literals[index]! with
      | .app _ (.base .not) inner => some (inner, rest)
      | positive => some (positive, .mkNot rest)
  let args ← (splitLamApp literal).2.toArray.mapM fun
    | .bvar index => some index
    | _ => none
  -- Distinct variable arguments make the definition a function definition.
  guard (args.toList.eraseDups.length == args.size)
  let mut abstracted ← abstractNamedBody args 0 named
  let (argSorts, _) := signature sort
  guard (argSorts.length == args.size)
  for argSort in argSorts.reverse do
    abstracted := .lam argSort abstracted
  pure abstracted

/-- Vampire's FOOL definition is the conjunction of two guarded equations,
possibly with a separate universal prefix on each branch. Recover a total
conditional, abstracting only the fresh symbol's distinct variable arguments.
The displayed definition is subsequently proved independently in Lean. -/
private def conditionalDefinitionValue? (symbol : LamTerm) (sort : LamSort)
    (formula : LamTerm) : Option LamTerm := do
  let peel : LamTerm → LamTerm := fun term => Id.run do
    let mut term := term
    while true do
      match term with
      | .app _ (.base (.forallE _)) (.lam _ body) => term := body
      | _ => return term
    return term
  let body := peel formula
  let .app _ (.app _ (.base .and) first) second := body | none
  let branch := fun term => do
    let .app _ (.app _ (.base .imp) condition) equation := peel term | none
    let (left, right) ← match equation with
      | .app _ (.app _ (.base (.eq _)) left) right => some (left, right)
      | .app _ (.app _ (.base .iff) left) right => some (left, right)
      | _ => none
    if (splitLamApp left).1 == symbol then some (condition, left, right)
    else if (splitLamApp right).1 == symbol then some (condition, right, left)
    else none
  let (firstCondition, firstApp, firstValue) ← branch first
  let (secondCondition, secondApp, secondValue) ← branch second
  guard (firstApp == secondApp)
  let (condition, left, right) ←
    if secondCondition == firstCondition.mkNot then some (firstCondition, firstValue, secondValue)
    else if firstCondition == secondCondition.mkNot then some (secondCondition, secondValue, firstValue)
    else none
  let args ← (splitLamApp firstApp).2.toArray.mapM fun
    | .bvar index => some index
    | _ => none
  guard (args.toList.eraseDups.length == args.size)
  let (argSorts, result) := signature sort
  guard (argSorts.length == args.size)
  let value := LamTerm.app result (.app result
    (.app (.base .prop) (.base (.ite result)) condition) left) right
  let mut abstracted ← abstractNamedBody args 0 value
  for argSort in argSorts.reverse do abstracted := .lam argSort abstracted
  pure abstracted

/-- Introduce a formula-naming predicate at its definition node, as a `let`
bound to the named subformula. -/
def withPredicateDefinitionLet (step : Step) (info : PredicateDefinitionInfo)
    (derived : Std.HashMap String DerivedSymbol) (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr → MetaM Expr) :
    MetaM Expr := do
  let some symbol := derived.get? info.symbol
    | throwError "named predicate `{info.symbol}` has no checked TFF declaration"
  unless symbol.kind == .predicateDefinition do
    throwError "fresh symbol `{info.symbol}` is not declared as a named predicate"
  let value? := if step.inference?.any (·.rule == "fool_ite_definition") then
    conditionalDefinitionValue? symbol.term symbol.sort step.formula
    else predicateDefinitionValue? symbol.term symbol.sort step.binders.size step.formula
  let some value := value?
    | throwError "definition `{step.name}` of `{symbol.name}` has no supported shape (`∀ x̄, φ ∨ ¬ {symbol.name}(x̄)`, `↔`, `=`, or `¬ {symbol.name}(t)`)"
  let expectedType ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms symbol.sort
  let value ← translateLocal typeAtoms termAtoms etoms value
  unless ← isDefEq (← inferType value) expectedType do
    throwError "predicate definition `{step.name}` does not match the TFF type of `{symbol.name}`"
  trace[vampire.replay] "named predicate let {symbol.name} : {expectedType} := {value}"
  withLetDecl (Name.mkSimple symbol.name) expectedType value fun symbolFVar => do
    let (termAtoms, etoms) := installDerivedSymbol symbol symbolFVar termAtoms etoms
    k termAtoms etoms (symbols.insert symbol.name symbolFVar)

/-- Introduce `p_flipped := fun x̄ => ¬ p x̄` for every flipped predicate and
let it stand for `p` in all later steps (see `PolarityFlips`). -/
partial def withPolarityFlipLets (heads : Array LamTerm) (index : Nat)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr) (symbols : Std.HashMap String Expr)
    (letFVars : Array Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr →
      Array Expr → MetaM Expr) : MetaM Expr := do
  if h : index < heads.size then
    let head := heads[index]
    let original ← translateLocal typeAtoms termAtoms etoms head
    let type ← inferType original
    let value ← forallTelescope type fun arguments body => do
      unless body.isProp do
        throwError "polarity-flipped symbol `{original}` is not a predicate"
      mkLambdaFVars arguments (mkNot (mkAppN original arguments))
    let name? := symbols.fold (init := none) fun found name value =>
      found <|> if value == original then some name else none
    let name := name?.getD s!"flipped{index}"
    trace[vampire.replay] "polarity flipping: `{name}` now denotes {value}"
    withLetDecl (Name.mkSimple s!"{name}_flipped") type value fun flipped => do
      let (termAtoms, etoms) ← match head with
        | .atom atom => pure (termAtoms.insert atom flipped, etoms)
        | .etom etom => pure (termAtoms, etoms.insert etom flipped)
        | _ => throwError "polarity-flipped predicate `{name}` is not a symbol"
      let symbols := if name?.isSome then symbols.insert name flipped else symbols
      withPolarityFlipLets heads (index + 1) typeAtoms termAtoms etoms symbols
        (letFVars.push flipped) k
  else
    k termAtoms etoms symbols letFVars

end VampireHammer.Replay.Internal

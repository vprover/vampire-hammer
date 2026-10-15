import Auto.Tactic
import VampireHammer.SourceNormalization
import VampireHammer.UnfoldingPlan

/-! Unfold definitions consistently across the instantiated problem.

A definition that is unfolded in one fact but folded in another separates the
two: `¬ b = c` cannot meet `IsLeftRegular a`, and a goal opened to
`∀ v w, G.Adj v w → …` cannot meet a premise about `G ≤ H`. Before
monomorphization, generic premises mention only `≤` of an arbitrary order,
so the alignment has to happen on the instantiated facts. This module provides
the extension that `Auto.Monomorphization.monomorphize` calls after saturation:

* A definition is *selected* when it was unfolded while introducing the goal,
  or when it occurs only in local facts (hypotheses and the negated goal) or
  only in premises. Occurrences are found through class projections of
  concrete instances, so `G ≤ H` at `SimpleGraph V` counts as
  `SimpleGraph.IsSubgraph G H`.
* Every instantiated fact that applies a selected proposition-valued
  definition gets an expanded copy. The folded fact is kept, since its expanded
  body may not be translatable.
* Each selected occurrence also gets its instantiated defining equation
  `∀ xs, c as = body` (`↔` for propositions), which connects the folded and
  the expanded forms even when only one of them is translatable.
* Unary functions of the problem that are inverse by definitional unfolding
  get `∀ x, g (f x) = x`, e.g. `(Quiver.Hom.unmop f).mop = f` or
  `e.symm.symm = e`.

All new facts are proved by reflexivity (checked by the kernel at replay) and
are optional: an untranslatable one is omitted. The returned facts are
saturated again, so definitions exposed by an expansion are selected in the
next round. -/

register_option vampire.alignInstantiatedDefinitions : Bool := {
  defValue := true
  descr := "After monomorphization, expand definitions that were unfolded in the goal or \
    occur on only one side of the problem in every instantiated fact, and add their \
    instantiated defining equations"
}

register_option vampire.definitionalInverses : Bool := {
  defValue := true
  descr := "Add `∀ x, g (f x) = x` for unary functions of the instantiated problem \
    that are inverse by definitional unfolding"
}

/-- Set by the tactic for the duration of one query: the definitions unfolded
while introducing the goal, separated by spaces. -/
register_option vampire.goalDefinitions : String := {
  defValue := ""
  descr := "Internal: definitions unfolded while introducing the current goal"
}

namespace VampireHammer.Export.DefinitionAlignment

open Lean Meta

def labelPrefix : String := "definition alignment "
def inverseLabelPrefix : String := "definitional inverse "

/-- Definitions selected per round, expanded copies per round, equations per
round, functions compared for inverses. -/
private def maxSelected : Nat := 8
private def maxCopies : Nat := 64
private def maxEquations : Nat := 32
private def maxFunctions : Nat := 32
private def maxGrowth : Nat := 4096

private inductive Side where
  | local | premise | neutral
  deriving BEq, Inhabited

private def Side.tag : Side → String
  | .local => "[local]"
  | .premise => "[premise]"
  | .neutral => "[neutral]"

/-- Hypotheses and the negated goal (`lctxLem`) versus explicit premises
(`❰term❱`). Automatically added facts belong to neither side. -/
private partial def side : Auto.DTr → Side
  | .leaf label =>
    -- `Premises` labels the negated goal separately from other hypotheses.
    if label.startsWith "lctxLem " || label.startsWith "vampire required negated goal" ||
        label.startsWith (labelPrefix ++ Side.local.tag) then .local
    else if label.startsWith "❰" || label.startsWith (labelPrefix ++ Side.premise.tag) then .premise
    else .neutral
  | .node _ premises => premises.foldl (fun found deriv =>
      if found != .neutral then found else side deriv) .neutral

private def excludedNames : Array Name := #[
  ``Not, ``Ne, ``Iff, ``And, ``Or, ``Exists, ``Eq, ``HEq, ``True, ``False, ``ite, ``dite,
  ``decide, ``id, ``outParam, ``optParam, ``autoParam, ``inferInstance, `inferInstanceAs]

/-- Non-recursive definitions other than instances, projections, matchers and
logical connectives. -/
private def eligible (name : Name) : MetaM Bool := do
  if excludedNames.contains name || name.isInternalDetail || (`Auto).isPrefixOf name then
    return false
  let env ← getEnv
  let some (.defnInfo info) := env.find? name | return false
  if (← isInstance name) || (← getProjectionFnInfo? name).isSome || isMatcherCore env name then
    return false
  -- Recursion, matchers and quotient primitives do not expand to a formula
  -- of the problem's vocabulary; their bodies only add opaque machinery.
  return (info.value.find? fun e => match e with
    | .const used _ => used == name || isAuxRecursor env used || isRecCore env used ||
        isMatcherCore env used || used == ``WellFounded.fix ||
        (match env.find? used with | some (.quotInfo _) => true | _ => false)
    | _ => false).isNone

private def unfoldOnce (e : Expr) : MetaM (Option Expr) := do
  let some body ← withTransparency .all <| unfoldDefinition? e | return none
  return some (← Core.betaReduce body)

/-- The definition applied by `e` and `e` with one layer of it expanded.
Class projections of concrete instances are reduced first; a proposition such
as `G ≤ H` whose instance field is written inline (`le x y := ∀ v w, …`) is
keyed by the projection itself (`LE.le`). -/
private partial def definitionStep? (e : Expr) (fuel : Nat := 4) : MetaM (Option (Name × Expr)) := do
  let .const name _ := e.getAppFn | return none
  if ← eligible name then
    let some body ← unfoldOnce e | return none
    return some (name, body)
  if fuel == 0 then return none
  let some info ← getProjectionFnInfo? name | return none
  unless info.fromClass do return none
  let some reduced ← withTransparency .instances <| unfoldProjInst? e | return none
  let reduced ← Core.betaReduce reduced
  if let some step ← definitionStep? reduced (fuel - 1) then return some step
  unless ← (try Meta.isProp e catch _ => pure false) do return none
  if reduced.getAppFn.isConstOf name then return none
  return some (name, reduced)

/-- `∀ xs, a = a`, `∀ xs, a ↔ a` or `∀ xs, True`: no information, but a
larger search space. -/
private def isTautology (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    if body.isTrue then return true
    if let some (_, lhs, rhs) := body.eq? then return lhs == rhs
    if let some (lhs, rhs) := body.iff? then return lhs == rhs
    return false

private def isEquation : Auto.DTr → Bool
  | .leaf label => label.startsWith labelPrefix && (label.splitOn " equation of ").length > 1
  | _ => false

/-- `binders`, restricted to those `e` or the retained binders' types use. -/
private def usedBinders (binders : Array Expr) (e : Expr) : MetaM (Array Expr) := do
  let mut kept := #[]
  let mut needed := collectFVars {} e
  for binder in binders.reverse do
    if needed.fvarSet.contains binder.fvarId! then
      kept := kept.push binder
      needed := collectFVars needed (← inferType binder)
  return kept.reverse

private structure Occurrence where
  name : Name
  isProp : Bool
  side : Side
  /-- The defining equation, closed over the fact's binders it uses. -/
  equation : Option Auto.Lemma

/-- Applications of eligible definitions in `fact`, with the instantiated
defining equation at each distinct occurrence. -/
private def occurrences (fact : Auto.Lemma) (wanted : Name → Bool) : MetaM (Array Occurrence) := do
  let original ← getLCtx
  let found ← IO.mkRef (#[] : Array Occurrence)
  let factSide := side fact.deriv
  let _ ← Meta.transform fact.type (pre := fun e => do
    unless e.isApp || e.isConst do return .continue e
    let some (name, body) ← definitionStep? e | return .continue e
    let isProp ← try Meta.isProp e catch _ => pure false
    let equation ← if !wanted name then pure none else
      try
        let binders := (← getLCtx).getFVars.filter fun x => !original.contains x.fvarId!
        let statement ← if isProp then pure (mkIff e body) else mkEq e body
        let kept ← usedBinders binders statement
        let refl ← if isProp then pure (mkApp (mkConst ``Iff.refl) e) else mkEqRefl e
        let proof ← mkLambdaFVars kept (← mkExpectedTypeHint refl statement)
        let type ← SourceNormalization.normalizeSyntax (← mkForallFVars kept statement)
        if ← isTautology type then pure none else
        pure (some ⟨⟨proof, type, .leaf s!"{labelPrefix}{factSide.tag} equation of {name}"⟩, #[]⟩)
      catch _ => pure none
    found.modify (·.push { name, isProp, side := factSide, equation })
    return .continue e)
  found.get

/-- The fact with one layer of the selected proposition-valued definitions
expanded, or `none` if nothing changes. -/
private def expand (selected : Array Name) (fact : Auto.Lemma) : MetaM (Option Auto.Lemma) := do
  -- Expanding a defining equation only yields `body ↔ body`.
  if isEquation fact.deriv then return none
  let type ← Meta.transform fact.type (post := fun e => do
    let some (name, body) ← definitionStep? e | return .done e
    unless selected.contains name do return .done e
    unless ← (try Meta.isProp e catch _ => pure false) do return .done e
    return .done body)
  let type ← SourceNormalization.normalizeSyntax type
  if type == fact.type || type.sizeWithoutSharing > fact.type.sizeWithoutSharing + maxGrowth ||
      (← isTautology type) then
    return none
  let label := s!"{labelPrefix}{(side fact.deriv).tag} {selected.toList} in {fact.deriv}"
  return some ⟨⟨← mkExpectedTypeHint fact.proof type, type, .leaf (label.take 300).toString⟩, #[]⟩

/-- Consistent unfolding of the instantiated facts, see the module comment. -/
def alignDefinitions (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let goalDefinitions := (vampire.goalDefinitions.get (← getOptions)).splitOn " "
    |>.filter (!·.isEmpty) |>.map String.toName
  let facts := facts.filter (·.params.isEmpty)
  -- First pass: where does each definition occur?
  let mut sides : Std.HashMap Name (Bool × Bool) := {}
  for fact in facts do
    for occurrence in ← occurrences fact (fun _ => false) do
      let (inLocal, inPremise) := sides.getD occurrence.name (false, false)
      sides := sides.insert occurrence.name
        (inLocal || occurrence.side == .local, inPremise || occurrence.side == .premise)
  let mut selected := #[]
  for (name, inLocal, inPremise) in sides.toArray do
    if selected.size >= maxSelected then break
    if goalDefinitions.contains name || inLocal != inPremise then
      selected := selected.push name
  if selected.isEmpty then return #[]
  trace[vampire.unfold] "Aligning instantiated facts on {selected}"
  let mut added := #[]
  let mut equations : Std.HashSet Expr := {}
  let mut copies := 0
  for fact in facts do
    for occurrence in ← occurrences fact selected.contains do
      let some equation := occurrence.equation | continue
      if equations.size >= maxEquations || equations.contains equation.type then continue
      equations := equations.insert equation.type
      added := added.push equation
    if copies >= maxCopies then continue
    if let some copy ← expand selected fact then
      copies := copies + 1
      added := added.push copy
  return added

/-- Closed unary functions `f : α → β` applied in the facts. -/
private def unaryFunctions (facts : Array Auto.Lemma) : MetaM (Array Expr) := do
  let original ← getLCtx
  let found ← IO.mkRef (#[] : Array Expr)
  for fact in facts do
    let _ ← Meta.transform fact.type (pre := fun e => do
      if (← found.get).size >= maxFunctions then return .done e
      let .app function _ := e | return .continue e
      if function.hasAnyFVar (fun id => !original.contains id) || (← found.get).contains function then
        return .continue e
      let type ← try whnfR (← inferType function) catch _ => return .continue e
      if let .forallE _ domain codomain _ := type then
        if !codomain.hasLooseBVars && !(← isProp domain) && !(← isProp e) then
          found.modify (·.push function)
      return .continue e)
  found.get

/-- `∀ x y, f x = f y → x = y` when `f` is, up to unfolding, the projection of
a structure with a single field: `x` is `⟨f x⟩` by structure eta, so the
constructor is a left inverse even when it does not occur in the problem
(`Quiver.Hom.unmop`, `Opposite.unop`, `Multiplicative.toAdd`). -/
private def projectionInjectivity? (f : Expr) : MetaM (Option Auto.Lemma) := do
  let saved ← saveState
  -- `try` does not catch the heartbeat limit.
  tryCatchRuntimeEx (Auto.Meta.withMaxHeartbeats 2000 <| withNewMCtxDepth do
      let .forallE _ domain _ _ ← whnfR (← inferType f) | return none
      let structureType ← whnf domain
      let .const structureName levels := structureType.getAppFn | return none
      let env ← getEnv
      let some info := getStructureInfo? env structureName | return none
      unless info.fieldNames.size == 1 && !(← isClass? structureType).isSome do return none
      let some (.inductInfo inductiveInfo) := env.find? structureName | return none
      let [constructor] := inductiveInfo.ctors | return none
      let parameters := structureType.getAppArgs.extract 0 inductiveInfo.numParams
      let mk := mkAppN (mkConst constructor levels) parameters
      withLocalDeclD `x domain fun x => withLocalDeclD `y domain fun y => do
        unless ← withTransparency .default <|
            isDefEq (mkApp f x) (.proj structureName 0 x) do return none
        let premise ← mkEq (mkApp f x) (mkApp f y)
        withLocalDeclD `h premise fun h => do
          let statement ← mkEq x y
          let lifted ← mkCongrArg mk h
          let proof ← mkLambdaFVars #[x, y, h] (← mkExpectedTypeHint lifted statement)
          let type ← mkForallFVars #[x, y] (← mkArrow premise statement)
          return some ⟨⟨proof, type, .leaf s!"{inverseLabelPrefix}injective {f}"⟩, #[]⟩)
    fun error => do
      if error.isInterrupt then throw error
      saved.restore
      return none

/-- `∀ x, g (f x) = x` for functions of the facts that are inverse by unfolding. -/
def definitionalInverses (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let functions ← unaryFunctions facts
  let mut added := #[]
  for f in functions do
    let .forallE _ domain codomain _ ← whnfR (← inferType f) | continue
    for g in functions do
      let .forallE _ domain' codomain' _ ← whnfR (← inferType g) | continue
      let saved ← saveState
      let inverse ← tryCatchRuntimeEx
        (Auto.Meta.withMaxHeartbeats 2000 <| withNewMCtxDepth <| withTransparency .default do
          unless ← isDefEq codomain domain' <&&> isDefEq codomain' domain do return none
          withLocalDeclD `x domain fun x => do
            let composite := mkApp g (mkApp f x)
            unless ← isDefEq composite x do return none
            let statement ← mkEq composite x
            return some (← mkForallFVars #[x] statement,
              ← mkLambdaFVars #[x] (← mkExpectedTypeHint (← mkEqRefl x) statement)))
        fun error => do if error.isInterrupt then throw error else pure none
      saved.restore
      if let some (type, proof) := inverse then
        trace[vampire.unfold] "Definitional inverse: {type}"
        added := added.push ⟨⟨proof, type, .leaf s!"{inverseLabelPrefix}{g} ∘ {f}"⟩, #[]⟩
    if let some injective ← projectionInjectivity? f then
      trace[vampire.unfold] "Definitional injectivity: {injective.type}"
      added := added.push injective
  return added

/-- The extension passed to `Auto.Monomorphization.monomorphize`. -/
def extend (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let options ← getOptions
  let goalDefinitions := (vampire.goalDefinitions.get options).splitOn " "
    |>.filter (!·.isEmpty) |>.map String.toName |>.toArray
  let aligned ← if vampire.unfoldingPlan.get options then
      UnfoldingPlan.expandInstantiated facts goalDefinitions
    else if vampire.alignInstantiatedDefinitions.get options then alignDefinitions facts
    else pure #[]
  let inverses ← if vampire.definitionalInverses.get options then
    definitionalInverses facts else pure #[]
  return aligned ++ inverses

end VampireHammer.Export.DefinitionAlignment

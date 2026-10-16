import Auto.Tactic
import VampireHammer.SourceNormalization
import VampireHammer.FactReporting

/-! A problem-level decision of which definitions to unfold.

A definition unfolded in one fact but folded in another separates the two
for the prover: `y ∈ f '' s` opened to `∃ x, x ∈ s ∧ f x = y` cannot meet a
fact about `f '' s`. Deciding per fact, under per-fact budgets, produces such
mixtures whenever two facts take different decisions. Following lean-auto's
`u[...]` instruction and the problem-wide lambda translation of Sledgehammer,
the decision is taken once per *symbol* for the whole problem:

* A definition is *planned* when one of its applications anywhere in the
  problem cannot be a first-order symbol application (a function or
  proposition argument, `SourceNormalization.hasHigherOrderArgument`), when
  it occurs on only one side of the problem (only in the hypotheses and the
  negated goal, or only in the explicit premises), where folded it could never
  meet the other side, or when the caller asks for it (definitions opened
  while introducing the goal).
* Planned definitions are unfolded in every fact, wherever they occur and
  whatever their arguments. Their bodies can expose further definitions; the
  plan is closed under this by iterating to a fixed point.
* A definition whose expansion somewhere would introduce a bound proof
  argument or a lambda over a proof of a bound-variable proposition, or grow a
  fact beyond a fixed bound, is rejected for the whole
  problem and stays folded everywhere. A definition that an explicit premise
  concludes (`IsSheaf` for `isSheaf_comp_of_isSheaf`) is never requested: the
  premise is stated in its terms.

Applications are found through class projections of concrete instances, so
`x ∈ s` at `Set α` is an application of `Set.Mem`. Recursive definitions,
matchers and quotient primitives are never unfolded: their bodies add
machinery, not vocabulary of the problem. Unfolding is definitional; facts keep
their proofs. -/

/-- Set by the tactic for one query: definitions concluded by explicit premise
constants, separated by spaces. The plan does not force them open. -/
register_option vampire.foldedDefinitions : String := {
  defValue := ""
  descr := "Internal: definitions concluded by the explicit premises of the current query"
}

namespace VampireHammer.UnfoldingPlan

open Lean Meta

/-- Bounds: planned definitions, fixed-point rounds, expression growth of one
expansion, and expansions within one fact. -/
private def maxPlanned : Nat := 48
private def maxRounds : Nat := 8
private def maxGrowth : Nat := 4096
private def maxSteps : Nat := 512
/-- Growth of one fact under the whole plan. -/
private def maxFactGrowth : Nat := 8192

private def excludedNames : Array Name := #[
  ``Not, ``Ne, ``Iff, ``And, ``Or, ``Exists, ``Eq, ``HEq, ``True, ``False, ``ite, ``dite,
  ``decide, ``Decidable.decide, ``id, ``outParam, ``optParam, ``autoParam, ``inferInstance,
  `inferInstanceAs]

/-- Non-recursive definitions other than instances, projections, matchers and
logical connectives. -/
def eligible (name : Name) : MetaM Bool := do
  -- Private definitions are ordinary definitions with mangled names.
  if excludedNames.contains name || (name.isInternalDetail && !isPrivateName name) ||
      (`Auto).isPrefixOf name then
    return false
  let env ← getEnv
  let some (.defnInfo info) := env.find? name | return false
  if (← isInstance name) || (← getProjectionFnInfo? name).isSome || isMatcherCore env name then
    return false
  -- Definitions that build instances (`Function.Injective.preorder`) are
  -- plumbing between a class operation and its field, not vocabulary.
  if ← forallTelescopeReducing info.type fun _ result => return (← isClass? result).isSome then
    return false
  return (info.value.find? fun e => match e with
    | .const used _ => used == name || isAuxRecursor env used || isRecCore env used ||
        isMatcherCore env used || used == ``WellFounded.fix ||
        (match env.find? used with | some (.quotInfo _) => true | _ => false)
    | _ => false).isNone

private def unfoldOnce (e : Expr) : MetaM (Option Expr) := do
  let some body ← withTransparency .all <| unfoldDefinition? e | return none
  return some (← Core.betaReduce body)

/-- Whether `e` may be an application handled by `step?`: a cheap filter. -/
private def candidateHead (e : Expr) : MetaM Bool := do
  let .const name _ := e.getAppFn | return false
  if SourceNormalization.logicalHeads.contains name then return false
  match (← getEnv).find? name with
  | some (.defnInfo _) => return true
  | _ => return false

/-- The definition applied by `e` and `e` with one layer of it expanded.
Class projections of concrete instances are reduced first; a projection whose
instance field is written inline (`le x y := ∀ v w, …`) is keyed by the
projection and the instance (`LE.le.SimpleGraph.instLE`). -/
partial def step? (e : Expr) (fuel : Nat := 4) : MetaM (Option (Name × Expr)) := do
  let .const name _ := e.getAppFn | return none
  if ← eligible name then
    let some body ← unfoldOnce e | return none
    return some (name, body)
  if fuel == 0 then return none
  let some info ← getProjectionFnInfo? name | return none
  unless info.fromClass do
    -- A field of a constructed value, such as the `toFun` of `(1 : M →*₀ N)`
    -- behind its coercion: the projection of a constructor application.
    let some value := e.getAppArgs[info.numParams]? | return none
    let value ← whnfD value
    unless value.isAppOf info.ctorName do return none
    let some field := value.getAppArgs[info.numParams + info.i]? | return none
    let extra := e.getAppArgs.extract (info.numParams + 1) e.getAppNumArgs
    return some (name, (mkAppN field extra).headBeta)
  -- Instances built by definitions such as `Function.Injective.preorder`
  -- only reduce to their field at default transparency.
  let reduced? ← withTransparency .instances <| unfoldProjInst? e
  let reduced? ← match reduced? with
    | some reduced => pure (some reduced)
    | none => withTransparency .default <| unfoldProjInst? e
  let some reduced := reduced? | return none
  let reduced ← Core.betaReduce reduced
  if let some step ← step? reduced (fuel - 1) then return some step
  if reduced.getAppFn.isConstOf name then return none
  -- Only a field that opens to a formula or a function exposes structure.
  -- Another constant (`Nat.le` for `≤` on `ℕ`, an inductive predicate the
  -- prover interprets) or a literal (`0 : ℕ`) would only rename the symbol.
  let opens := match reduced.getAppFn with
    | .lam .. | .forallE .. => true
    | .const head _ => SourceNormalization.logicalHeads.contains head
    | _ => false
  unless opens do return none
  -- An instance whose field is written inline: one key per projection and
  -- instance, whatever the type of the application, so that `{a}` and
  -- `{a} x` at `Set` are decided together and `Finset`'s `{a}` separately.
  let .const instanceName _ := (e.getArg! info.numParams).getAppFn | return none
  return some (name ++ instanceName, reduced)

/-- `∀ xs, a = a`, `∀ xs, a ↔ a` or `∀ xs, True`. -/
def isTautology (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    if body.isTrue then return true
    if let some (_, lhs, rhs) := body.eq? then return lhs == rhs
    if let some (lhs, rhs) := body.iff? then return lhs == rhs
    return false

/-- Whether the application `e`, keyed `key`, is planned. A requested
projection name (`Singleton.singleton`, from the goal's introduction) covers
its applications at every instance, whatever definition they reach. -/
private def isPlanned (planned : Array Name) (e : Expr) (key : Name) : Bool :=
  planned.any fun name => name == key || name.isPrefixOf key || e.getAppFn.isConstOf name

/-- `type` with every application of a planned definition expanded, to the
bottom: bodies are traversed again, so nested planned definitions open too. -/
def apply (planned : Array Name) (type : Expr) : MetaM Expr := do
  if planned.isEmpty then return type
  let steps ← IO.mkRef maxSteps
  let type ← Meta.transform type (post := fun e => do
    if (← steps.get) == 0 then return .done e
    unless ← candidateHead e do return .done e
    let some (name, body) ← (try step? e catch _ => pure none) | return .done e
    unless isPlanned planned e name do return .done e
    steps.modify (· - 1)
    return .visit body)
  -- Definition bodies can carry metadata, which monomorphization rejects.
  let type := type.replace fun e => if let .mdata _ inner := e then some inner.consumeMData else none
  SourceNormalization.normalizeSyntax type

/-- `x` within a heartbeat budget for one fact; `fallback` if it fails or runs
out (`try` does not catch the heartbeat limit). -/
private def bounded (x : MetaM α) (fallback : α) : MetaM α := do
  let saved ← saveState
  tryCatchRuntimeEx (Auto.Meta.withMaxHeartbeats 4000 x) fun error => do
    if error.isInterrupt then throw error
    saved.restore
    pure fallback

/-- `type` with the plan applied, or unchanged if the expansion fails. -/
private def applyBounded (planned : Array Name) (type : Expr) : MetaM Expr :=
  bounded (apply planned type) type

/-- Hypotheses and the negated goal versus explicit premises (`❰term❱`).
Automatically added facts belong to neither side. -/
inductive Side where
  | local | premise | neutral
  deriving BEq, Inhabited

partial def side : Auto.DTr → Side
  | .leaf label =>
    if label.startsWith "lctxLem " || label.startsWith "vampire required negated goal" then .local
    else if label.startsWith "❰" then .premise
    else .neutral
  | .node _ premises => premises.foldl (fun found deriv =>
      if found != .neutral then found else side deriv) .neutral

/-- How a definition occurs in the problem. -/
private structure Usage where
  blocked : Bool := false
  inLocal : Bool := false
  inPremise : Bool := false
  rejected : Bool := false

/-- Whether `expression` binds a proof whose proposition depends on bound
variables in a lambda (`fun (h : t ∈ S) => …`, as in `⋂ t ∈ S, ↑t`). lean-auto
cannot abstract such a binder; a definition exposing one stays folded. -/
private def hasDependentProofLambda (expression : Expr) (original : LocalContext) : MetaM Bool := do
  let found ← IO.mkRef false
  let _ ← Meta.transform expression (pre := fun expression => do
    if ← found.get then return .done expression
    if let .lam _ type _ _ := expression then
      if type.hasAnyFVar (fun id => !original.contains id) then
        if ← (try Meta.isProp type catch _ => pure false) then
          found.set true
          return .done expression
    return .continue expression)
  found.get

/-- Record the definitions applied in `type`, a fact of side `factSide`. -/
private def scan (type : Expr) (factSide : Side)
    (usages : IO.Ref (Std.HashMap Name Usage)) : MetaM Unit := do
  let original ← getLCtx
  let _ ← Meta.transform type (pre := fun e => do
    unless ← candidateHead e do return .continue e
    let some (name, body) ← (try step? e catch _ => pure none) | return .continue e
    let usage := (← usages.get).getD name {}
    let blocked ← pure usage.blocked <||> SourceNormalization.hasHigherOrderArgument e
    let rejected ← pure usage.rejected <||>
      pure (body.sizeWithoutSharing > e.sizeWithoutSharing + maxGrowth) <||>
      SourceNormalization.hasBoundProofArgument body original <||>
      hasDependentProofLambda body original
    let inLocal := usage.inLocal || factSide == Side.local
    let inPremise := usage.inPremise || factSide == Side.premise
    usages.modify (·.insert name { blocked, rejected, inLocal, inPremise })
    return .continue e)

/-- The definitions to unfold in the problem `facts`, see the module comment.
A definition is planned when an application cannot be first-order, when it is
`requested`, or when it occurs on only one side of the problem: folded there,
it could never meet the other side. -/
def plan (facts : Array (Expr × Side)) (requested : Array Name := #[]) : MetaM (Array Name) := do
  -- A definition that an explicit premise concludes is not forced open: the
  -- premise is stated in its terms. It still opens if it occurs on one side only.
  let folded := (vampire.foldedDefinitions.get (← getOptions)).splitOn " "
    |>.filter (!·.isEmpty) |>.map String.toName |>.toArray
  let mut planned : Array Name := requested.filter (!folded.contains ·)
  let mut rejected : Array Name := #[]
  let mut current := facts
  for _ in [:maxRounds] do
    let usages ← IO.mkRef ({} : Std.HashMap Name Usage)
    for (type, factSide) in current do
      bounded (scan type factSide usages) ()
    let usages := (← usages.get).toArray
    let newlyRejected := usages.filterMap fun (name, usage) =>
      if usage.rejected && !rejected.contains name then some name else none
    rejected := rejected ++ newlyRejected
    -- A definition already unfolded elsewhere cannot be withdrawn piecemeal:
    -- start over from the original facts without it.
    if newlyRejected.any planned.contains then
      planned := planned.filter (!rejected.contains ·)
      current ← facts.mapM fun (type, factSide) => return (← applyBounded planned type, factSide)
      continue
    let additions := usages.filterMap fun (name, usage) =>
      if !usage.rejected && !rejected.contains name && !planned.contains name &&
          (usage.blocked || usage.inLocal != usage.inPremise) then some name else none
    -- Each expansion is bounded, but a chain of them (`IsSheaf`, `IsSheafFor`,
    -- `FamilyOfElements`, …) can still blow a fact up: reject a definition
    -- whose expansion, with the plan so far, grows a fact beyond the bound.
    let mut accepted := #[]
    for name in additions do
      let mut grows := false
      for ((type, _), (original, _)) in current.zip facts do
        unless (type.find? fun e => e.getAppFn.isConstOf name).isSome do continue
        let expanded ← applyBounded (planned.push name) type
        if expanded.sizeWithoutSharing > original.sizeWithoutSharing + maxFactGrowth then
          grows := true
          break
      if grows then rejected := rejected.push name else accepted := accepted.push name
    let additions := accepted
    if additions.isEmpty then break
    if planned.size + additions.size > maxPlanned then
      trace[vampire.unfold] "Unfolding plan is full; keeping {additions} folded"
      break
    planned := planned ++ additions
    current ← facts.mapM fun (type, factSide) => return (← applyBounded planned type, factSide)
  trace[vampire.unfold] "Unfolding plan: {planned}; kept folded: {rejected}"
  return planned

/-- Apply a plan to source facts, which keep their proofs (the expansion is
definitional). Facts that become tautologies are dropped. -/
def applyToLemmas (planned : Array Name) (lemmas : Array Auto.Lemma) :
    MetaM (Array Auto.Lemma) := do
  if planned.isEmpty then return lemmas
  lemmas.filterMapM fun lemma => do
    let type ← applyBounded planned lemma.type
    if type == lemma.type then return some lemma
    trace[vampire.unfold] "Planned unfolding of {lemma.deriv}: {type}"
    if ← isTautology type then return none
    -- Expansions can bind subtype elements (`Set.range` of a function on `↥s`).
    let proof := FactReporting.markUnfolded planned type lemma.proof
    return some (← SubtypeRelativization.relativize { lemma with type, proof })

/-- After monomorphization, instantiation creates applications of definitions
that the generic facts did not show (`s ≤ t` of an arbitrary order becomes
`Set.Subset s t`). The same plan, recomputed on the instantiated facts, gives
each fact still containing a planned definition its expanded copy; the
monomorphization extension can only add facts. -/
def expandInstantiated (facts : Array Auto.Lemma) (requested : Array Name) :
    MetaM (Array Auto.Lemma) := do
  let facts := facts.filter (·.params.isEmpty)
  let planned ← plan (facts.map fun fact => (fact.type, side fact.deriv)) requested
  if planned.isEmpty then return #[]
  let mut copies := #[]
  for fact in facts do
    let type ← applyBounded planned fact.type
    if type == fact.type || (← isTautology type) || facts.any (·.type == type) ||
        copies.any (·.type == type) then
      continue
    let label := s!"unfolding plan {planned.toList} in {fact.deriv}"
    copies := copies.push (← SubtypeRelativization.relativize
      ⟨⟨FactReporting.markUnfolded planned type (← mkExpectedTypeHint fact.proof type), type, .leaf (label.take 300).toString⟩, #[]⟩)
  trace[vampire.unfold] "Expanded {copies.size} instantiated facts with {planned}"
  return copies

end VampireHammer.UnfoldingPlan

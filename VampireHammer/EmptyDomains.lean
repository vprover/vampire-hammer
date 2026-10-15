import VampireHammer.UnfoldingPlan
import VampireHammer.Export.Inhabitation
import VampireHammer.Replay.Diagnostics
import VampireHammer.Export.Diagnostics

/-! Witnesses for possibly empty types, searched only when a proof needs one.

The prover's sorts are nonempty, so a problem that quantifies over a type
variable `α` without an inhabitant cannot be exported (`IsSMulRegular (ULift R)
r ↔ IsSMulRegular R r` holds for empty `R` too). Rather than searching for an
inhabitant before the proof search starts, the goal is proved under the
assumption `h : Nonempty α` (with an `Inhabited α` instance, so that `α` and
types built from it such as `ULift α` have witnesses):

1. if the proof does not use `h`, it proves the goal as it is;
2. otherwise the goal is split on `Nonempty α`. In the empty case a type `T`
   with a projection to `α` (`α` itself, `ULift α`, `{x // p x}`, `α × β`) has
   no elements: after opening proposition-valued definitions, `∀ x : T, P x`
   is rewritten to `True` and `∃ x : T, P x` to `False` by checked equations,
   and `simp` simplifies the rest. Anything left goes back to the hammer. -/

namespace VampireHammer.EmptyDomains

open Lean Meta

/-- Local type variables for which the cheap witness recovery finds nothing:
no local of the type, no `Nonempty` instance, and no short application of local
functions (`f a` for `f : α → β`). -/
def candidates : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let locals := lctx.foldl (init := #[]) fun locals decl =>
    if decl.isImplementationDetail then locals else locals.push decl.toExpr
  let mut found := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let .sort level ← whnf decl.type | continue
    if level.isZero then continue
    let type := decl.toExpr
    if let .some _ ← trySynthInstance (mkApp (.const ``Nonempty [level]) type) then continue
    let saved ← saveState
    let witness? ← Export.Internal.localDomainWitness type locals (← IO.mkRef 64) 3
    saved.restore
    if witness?.isSome then continue
    found := found.push type
  return found

/-- `x ↦ e x : T → type`, for `T` the type itself or a structure with a field
of that type (`ULift`, `Subtype`, `Prod`). -/
private partial def projection? (domain type : Expr) (depth : Nat := 3) : MetaM (Option Expr) := do
  if ← isDefEq domain type then
    return some (← withLocalDeclD `x domain fun x => mkLambdaFVars #[x] x)
  if depth == 0 then return none
  let .const name _ := (← whnfR domain).getAppFn | return none
  let env ← getEnv
  unless isStructure env name do return none
  withLocalDeclD `x domain fun x => do
    for field in getStructureFieldsFlattened env name (includeSubobjectFields := false) do
      let value ← try mkProjection x field catch _ => continue
      let fieldType ← inferType value
      if ← isProp fieldType then continue
      if let some down ← projection? fieldType type (depth - 1) then
        return some (← mkLambdaFVars #[x] (mkApp down value).headBeta)
    return none

/-- Types bound in `e` by `∀`, `fun` or `∃` that do not depend on bound
variables. -/
private def binderTypes (e : Expr) : Array Expr := Id.run do
  let mut found := #[]
  let mut pending := [e]
  while !pending.isEmpty do
    let sub :: rest := pending | break
    pending := rest
    let type? : Option Expr := match sub with
      | .forallE _ type _ _ | .lam _ type _ _ => some type
      | _ => if sub.isAppOfArity ``Exists 2 then some sub.appFn!.appArg! else none
    if let some type := type? then
      unless type.hasLooseBVars || found.contains type do found := found.push type
    pending := match sub with
      | .forallE _ type body _ | .lam _ type body _ => type :: body :: pending
      | .app fn arg => fn :: arg :: pending
      | .mdata _ inner => inner :: pending
      | .letE _ type value body _ => type :: value :: body :: pending
      | .proj _ _ inner => inner :: pending
      | _ => pending
  return found

/-- `∀ P, (∀ x, P x) = True` and `∀ P, (∃ x, P x) = False` for an empty
`domain`, from `empty : domain → False`. -/
private def emptinessEquations (domain empty : Expr) : MetaM (Array Expr) := do
  let .sort level ← whnf (← inferType domain) | return #[]
  let predicate ← mkArrow domain (mkSort .zero)
  withLocalDeclD `P predicate fun p => do
    let forallProof ← withLocalDeclD `x domain fun x => do
      mkLambdaFVars #[x] (← mkFalseElim (mkApp p x) (mkApp empty x))
    let forallEq ← mkLambdaFVars #[p] (← mkAppM ``eq_true #[forallProof])
    let existsType := mkApp2 (.const ``Exists [level]) domain p
    let existsProof ← withLocalDeclD `h existsType fun h => do
      let elim ← withLocalDeclD `x domain fun x => withLocalDeclD `hx (mkApp p x) fun hx => do
        mkLambdaFVars #[x, hx] (mkApp empty x)
      mkLambdaFVars #[h] (mkApp5 (.const ``Exists.elim [level]) domain p (mkConst ``False) h elim)
    let existsEq ← mkLambdaFVars #[p] (← mkAppM ``eq_false #[existsProof])
    return #[forallEq, existsEq]

/-- Open proposition-valued definitions of `type`, so that its quantifiers
become visible (`Function.Injective f`). A definitional change. -/
private def openPropositions (type : Expr) : MetaM Expr := do
  let steps ← IO.mkRef (64 : Nat)
  Meta.transform type (post := fun e => do
    if (← steps.get) == 0 then return .done e
    unless ← (try Meta.isProp e catch _ => pure false) do return .done e
    let some (_, body) ← (try UnfoldingPlan.step? e catch _ => pure none) | return .done e
    steps.modify (· - 1)
    return .visit body)

/-- Close as much of `goal` as the emptiness of `type` (`h : ¬ Nonempty type`)
gives; the remaining goal, if any. -/
private def simplifyEmptyCore (goal : MVarId) (type empty : Expr) : MetaM (Option MVarId) :=
  goal.withContext do
    let target ← openPropositions (← instantiateMVars (← goal.getType))
    let mut goal ← goal.replaceTargetDefEq target
    let mut domains := #[type] ++ binderTypes target
    -- Empty quantifiers in hypotheses can establish the goal too, and must
    -- disappear before the next export builds its signature.
    let declarations := (← getLCtx).getFVarIds
    for id in declarations do
      let decl ← id.getDecl
      if decl.isImplementationDetail || !(← isProp decl.type) then continue
      let opened ← openPropositions decl.type
      domains := domains ++ binderTypes opened
      goal ← goal.replaceLocalDeclDefEq id opened
    let mut theorems ← getSimpTheorems
    let mut instances := #[]
    for domain in domains do
      let some down ← projection? domain type | continue
      let eliminate ← withLocalDeclD `x domain fun x => do
        mkLambdaFVars #[x] (mkApp empty (mkApp down x).headBeta)
      -- Mathlib's aggregate and data simplifications use IsEmpty instances.
      -- Build them from the checked eliminator rather than assuming them.
      if (← getEnv).contains `IsEmpty then
        let classType ← mkAppM `IsEmpty #[domain]
        let value ← mkAppM `IsEmpty.mk #[eliminate]
        let (instanceId, inner) ← goal.note `vampireEmptyDomain value (some classType)
        goal := inner
        instances := instances.push (mkFVar instanceId)
      for equation in ← emptinessEquations domain eliminate do
        theorems ← theorems.add (.other `emptyDomain) #[] equation
    let context ← Simp.mkContext { maxSteps := 2048 } #[theorems] (← getSimpCongrTheorems)
    let saved ← saveState
    try
      let (result, _) ← goal.withContext <| withNewLocalInstances instances 0 <| simpAll goal context
      return result
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      saved.restore
      return some goal

private def simplifyEmpty (goal : MVarId) (type empty : Expr)
    (budget? : Option Export.SearchAllowance := none) : MetaM (Option MVarId) := do
  let budget ← match budget? with
    | some budget => pure budget
    | none => Export.SearchAllowance.create 4000
  let result ← budget.run (simplifyEmptyCore goal type empty)
  return result.getD (some goal)

def closeEmpty (goal : MVarId) (type : Expr) (h : FVarId)
    (budget? : Option Export.SearchAllowance := none) : MetaM (Option MVarId) :=
  goal.withContext do
    let empty ← withLocalDeclD `x type fun x => do
      mkLambdaFVars #[x] (mkApp (mkFVar h) (← mkAppM ``Nonempty.intro #[x]))
    simplifyEmpty goal type empty budget?

/-- A known-empty type is simplified directly, without asking the external
prover for a contradiction under an inconsistent nonempty assumption. -/
def simplifyKnownEmpty? (goal : MVarId) (type : Expr)
    (budget? : Option Export.SearchAllowance := none) : MetaM (Option (Option MVarId)) :=
  goal.withContext do
    let empty? ← withLocalDeclD `x type fun x => do
      -- IsEmpty is supplied by mathlib; keep the core-only library usable.
      if (← getEnv).contains `IsEmpty then
        if let .some inst ← trySynthInstance (← mkAppM `IsEmpty #[type]) then
          let proof ← mkAppOptM `IsEmpty.false #[some type, some inst, some x]
          return some (← mkLambdaFVars #[x] proof)
      if type.isConstOf ``Empty then
        return some (← mkLambdaFVars #[x] (← mkAppM ``Empty.elim #[x]))
      let nonempty ← mkAppM ``Nonempty #[type]
      let negative ← mkAppM ``Not #[nonempty]
      for decl in (← getLCtx) do
        if decl.isImplementationDetail then continue
        let saved ← saveState
        if ← isDefEq decl.type negative then
          let proof := mkApp decl.toExpr (← mkAppM ``Nonempty.intro #[x])
          return some (← mkLambdaFVars #[x] proof)
        saved.restore
      return none
    let some empty := empty? | return none
    return some (← simplifyEmpty goal type empty budget?)

/-- Prefer the actual missing exported type, including closed composites such
as a subtype or Fin n. Only types closed over the restored goal may be used. -/
def missingCandidates (message : MessageData) : MetaM (Array Expr) := do
  if let some type := Export.missingDomainType? message then
    let context ← getLCtx
    if !type.hasMVar && !type.hasLooseBVars &&
        (collectFVars {} type).fvarIds.all context.contains then
      return #[type]
  return (← candidates).extract 0 4

/-- `goal` under the assumption `h : Nonempty type`, with an `Inhabited type`
instance: the goal to prove, and the proof of `Nonempty type → goal` it fills. -/
def assume (goal : MVarId) (type : Expr) : MetaM (MVarId × Expr) := goal.withContext do
  let .sort level ← whnf (← inferType type) | throwError "{type} is not a type"
  let nonempty := mkApp (.const ``Nonempty [level]) type
  let assumed ← mkFreshExprSyntheticOpaqueMVar (mkForall `nonempty .default nonempty (← goal.getType))
  let (h, inner) ← assumed.mvarId!.intro1
  let inhabited := mkApp (.const ``Inhabited [level]) type
  let value := mkApp2 (.const ``Classical.inhabited_of_nonempty [level]) type (mkFVar h)
  let inner ← inner.assert `inhabited inhabited value
  let (_, inner) ← inner.intro1
  return (inner, assumed)

/-- Close `goal` with the proof `assumed : Nonempty type → goal` found under the
assumption. Unused, the assumption is dropped; otherwise the goal is split on
`Nonempty type`, and the empty case is returned if `closeEmpty` leaves anything. -/
def discharge (goal : MVarId) (type : Expr) (assumed : Expr)
    (budget? : Option Export.SearchAllowance := none) :
    MetaM (Option MVarId) := goal.withContext do
  -- The instance is a `let`-like application of the assumption; reduce it so
  -- that an unused instance does not count as a use.
  let proof ← Core.betaReduce (← instantiateMVars assumed)
  if let .lam _ _ body _ := proof then
    unless body.hasLooseBVars do
      trace[vampire] "The proof does not use the inhabitant of {type}"
      goal.assign body
      return none
  let .sort level ← whnf (← inferType type) | throwError "{type} is not a type"
  let (nonempty, empty) ← goal.byCases (mkApp (.const ``Nonempty [level]) type) `nonempty
  nonempty.mvarId.assign (mkApp proof (mkFVar nonempty.fvarId))
  closeEmpty empty.mvarId type empty.fvarId budget?

end VampireHammer.EmptyDomains

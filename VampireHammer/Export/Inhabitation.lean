import Auto.Tactic
import VampireHammer.Options
import VampireHammer.Replay.Diagnostics
import VampireHammer.Export.SearchBudget

register_option vampire.domainWitnessHeartbeats : Nat := {
  defValue := 4000
  descr := "Shared heartbeat allowance for optional local domain witness recovery per problem"
}

/-! Recover domain witnesses already implied by the source signature.
Every recovered witness is an ordinary Lean term. -/

namespace VampireHammer.Export.Internal

open Lean Meta Auto.Embedding.Lam

private def isDomain : LamSort → Bool
  | .atom _ | .base .nat | .base .int => true
  | _ => false

/-- Reject different rigid result heads before expensive unification. Aliases,
lets and metavariables retain the normal matching path. This also prevents
irrelevant functions from consuming the bounded application-attempt count. -/
private def rigidHead? (type : Expr) : MetaM (Option Name) := do
  match type.getAppFn with
  | .const name _ =>
    return if (← getEnv).find? name |>.any (·.isInductive) then some name else none
  | .fvar id =>
    let decl ← id.getDecl
    return if decl.isLet then none else some id.name
  | _ => return none

private def incompatibleResult (candidateType target : Expr) : MetaM Bool := do
  let mut result := candidateType
  while result.isForall do result := result.bindingBody!
  let some left ← rigidHead? result | return false
  let some right ← rigidHead? target | return false
  return left != right

/-- Logical values and constant functions can supply arguments without a
source constant of that exact sort. A function witness never establishes
inhabitation of its domain. -/
private partial def argumentWitness (sort : LamSort)
    (witnesses : Std.HashMap LamSort Expr) : Auto.LamReif.ReifM (Option Expr) := do
  if let some witness := witnesses.get? sort then return some witness
  match sort with
  | .base .prop => return some (mkConst ``True)
  | .func domain range =>
    let some value ← argumentWitness range witnesses | return none
    let (_, _, type, _) ← Auto.LamReif.updownFunc domain
    return some (mkLambda `_ .default type value)
  | _ => return none

/-- Recover a value using existing locals, including functions omitted from
the exported formulas. Search only their applications, with bounds on depth,
arity and candidate attempts. Failed matches restore all metavariable state. -/
partial def localDomainWitness (type : Expr) (candidates : Array Expr)
    (budget : IO.Ref Nat) (depth : Nat) : MetaM (Option Expr) := do
  let onlyFacts := vampire.onlyFacts.get (← getOptions)
  unless onlyFacts do
    if let some witness ← Auto.Meta.trySynthInhabited type then return some witness
  -- Inhabited itself can be a first-order domain (e.g. a hypothesis
  -- Inhabited α → P). A real Nonempty α justifies constructing its dictionary;
  -- a binder from a quantified premise must never stand in for that value.
  if !onlyFacts && type.isAppOfArity ``Inhabited 1 then
    let domain := type.getAppArgs[0]!
    let nonempty ← mkAppM ``Nonempty #[domain]
    if let .some proof ← trySynthInstance nonempty then
      return some (← mkAppM ``Classical.inhabited_of_nonempty #[proof])
  for candidate in candidates do
    let saved ← saveState
    if ← isDefEq (← inferType candidate) type then
      return some (← instantiateMVars candidate)
    saved.restore
  if depth == 0 then return none
  for candidate in candidates do
    let candidateType ← whnf (← inferType candidate)
    unless candidateType.isForall do continue
    if ← incompatibleResult candidateType type then continue
    if (← budget.get) == 0 then return none
    budget.modify (· - 1)
    let saved ← saveState
    let (args, _, result) ← forallMetaTelescopeReducing candidateType
    let mut usable := args.size <= 8 && (← isDefEq result type)
    if usable then
      for arg in args do
        let value ← instantiateMVars arg
        unless value.isMVar do continue
        let domain ← instantiateMVars (← inferType value)
        -- Do not search for types or invent polymorphic specializations.
        if domain.isSort then
          usable := false
          break
        let some witness ← localDomainWitness domain candidates budget (depth - 1) | do
          usable := false
          break
        value.mvarId!.assign witness
    if usable then
      let witness ← instantiateMVars (mkAppN candidate args)
      if !witness.hasExprMVar && !witness.hasLevelMVar then return some witness
    saved.restore
  return none

/-- Close inhabitation under source functions, preserving partially applied
function results for higher-order consumers. Cycles without a starting
witness derive nothing. Each pass adds a previously absent signature sort,
so closure terminates even when the source functions form cycles. -/
partial def deriveDomainInhabitants (shared? : Option Export.SearchAllowance := none) : Auto.LamReif.ReifM Unit := do
  let terms ← Auto.LamReif.getVarVal
  let inhabitants ← Auto.LamReif.getInhabitations
  let mut witnesses : Std.HashMap LamSort Expr := {}
  witnesses := witnesses.insert (.base .nat) (toExpr (0 : Nat))
  witnesses := witnesses.insert (.base .int) (toExpr (0 : Int))
  for (term, sort) in terms do
    if !witnesses.contains sort then witnesses := witnesses.insert sort term
  for (sort, (witness, _, _)) in inhabitants.toArray do
    if !witnesses.contains sort then witnesses := witnesses.insert sort witness
  -- Preprocessing/object encoding can introduce sorts after monomorphization's
  -- initial witness pass. Recover actual local values and existential witnesses
  -- even when they were not mentioned by an exported source formula.
  let missingTypes := ((← Auto.LamReif.getTyVal).map Prod.fst |>.zipIdx).filter
    (fun (_, index) => !witnesses.contains (.atom index))
  let mut localWitnesses := #[]
  let mut projected := 0
  unless missingTypes.isEmpty do
    for decl in (← getLCtx) do
      unless decl.isImplementationDetail do
        -- Unselected proof hypotheses must not supply hidden existential or
        -- Nonempty witnesses in `only` mode. Selected witnesses are already
        -- registered in the reification state.
        if vampire.onlyFacts.get (← getOptions) && (← isProp decl.type) then continue
        localWitnesses := localWitnesses.push (mkFVar decl.fvarId)
        let type ← whnf decl.type
        if type.isAppOf ``Exists then
          let witness ← mkAppM ``Classical.choose #[mkFVar decl.fvarId]
          localWitnesses := localWitnesses.push witness
        match type.getAppFn, type.getAppArgs with
        | .const ``Nonempty [u], #[α] =>
          localWitnesses := localWitnesses.push
            (mkApp2 (.const ``Classical.choice [u]) α (mkFVar decl.fvarId))
        | .const ``Inhabited [u], #[α] =>
          localWitnesses := localWitnesses.push
            (mkApp2 (.const ``Inhabited.default [u]) α (mkFVar decl.fvarId))
        | _, _ => pure ()
        -- Records and classes can carry values/functions without exporting
        -- them as logical facts. Project their data fields from the actual
        -- local value, using metadata rather than mathematical names.
        unless ← isProp type do
          let .const name _ := type.getAppFn | continue
          let env ← getEnv
          if (getStructureInfo? env name).isNone then continue
          for field in getStructureFieldsFlattened env name true do
            if projected >= 64 then break
            projected := projected + 1
            let saved ← liftM (show MetaM Meta.SavedState from saveState)
            try
              let value ← mkProjection (mkFVar decl.fvarId) field
              unless ← isProp (← inferType value) do
                localWitnesses := localWitnesses.push value
            catch error =>
              liftM saved.restore
              if error.isInterrupt || error.isRuntime then throw error
  let shared ← match shared? with
    | some shared => pure shared
    | none => liftM <| Export.SearchAllowance.create (vampire.domainWitnessHeartbeats.get (← getOptions))
  let budget ← IO.mkRef (64 : Nat)
  for (type, index) in missingTypes do
    let sort := LamSort.atom index
    if witnesses.contains sort then continue
    let witness? ← liftM <| shared.run (localDomainWitness type localWitnesses budget 3)
    if let some (some witness) := witness? then
      witnesses := witnesses.insert sort witness
  let mut changed := true
  while changed do
    changed := false
    for (function, sourceSort) in terms do
      let mut value := function
      let mut sort := sourceSort
      while sort.isFunc do
        let .func domain range := sort | break
        let some argument ← argumentWitness domain witnesses | break
        value := mkApp value argument
        sort := range
        if witnesses.contains sort then continue
        let (_, _, type, _) ← Auto.LamReif.updownFunc sort
        unless ← isDefEq (← inferType value) type do
          throwError "derived domain witness has an unexpected type; expected {type}"
        witnesses := witnesses.insert sort value
        changed := true
  -- Source constants also supply atomic witnesses, even when no application
  -- is necessary. Register them with the checked reification boundary.
  for (sort, witness) in witnesses.toArray do
    if isDomain sort then
      Auto.LamReif.newInhabitation witness (.leaf "source signature inhabitation") sort

end VampireHammer.Export.Internal

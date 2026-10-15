import Auto.Tactic
import VampireHammer.Export.SearchBudget

/-! Instantiate data arguments of premises with available values.

Monomorphization instantiates type and instance arguments from constants that
occur in the problem, but never a data argument: in
`Equiv.isEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α`, nothing in a goal
`IsEmpty (ULift α)` determines `β` or provides `e`, and the premise is dropped.
Library proofs supply such arguments explicitly, e.g.
`Equiv.isEmpty Equiv.ulift` or `FullyFaithful.faithful fullyFaithfulIncl`.

Given explicit premises and *witnesses* (non-proposition hints and local
bundled values), this module unifies each explicit binder of a premise whose
type is a bundled structure (`α ≃ β`, `M →* N`, `F.FullyFaithful`; not a
class, not a plain type variable) with

* a witness, after instantiating its own arguments with metavariables;
* the function coercion of a witness, and of `w.symm` for an equivalence,
  applied to a local bundled value (`⇑representableByEquiv.symm e`).

Type variables left open are then matched against the propositions of the goal
and the hypotheses. The instantiated premise keeps the original proof applied
to the witness; remaining metavariables are abstracted as universally
quantified variables for monomorphization. The facts are optional. -/

register_option vampire.dataWitnesses : Bool := {
  defValue := true
  descr := "Instantiate data arguments of explicit premises with non-proposition hints and local data"
}

register_option vampire.dataWitnessHeartbeats : Nat := {
  defValue := 4000
  descr := "Shared heartbeat allowance for optional data-witness instantiation (0 disables it)"
}

namespace VampireHammer.Export.DataWitnesses

open Lean Meta

def labelPrefix : String := "data witness "

/-- A closed value, possibly a function of its implicit arguments. -/
structure Witness where
  value : Expr
  type : Expr
  params : Array Name
  label : String
  /-- A local value is already a term of the problem. -/
  isLocal : Bool := false

private def maxFacts : Nat := 16
private def maxLocals : Nat := 16

/-- Distinct structure constructors cannot become definitionally equal.
Open type variables and aliases retain the ordinary unification path. -/
private def compatibleStructureHeads (left right : Expr) : MetaM Bool := do
  let env ← getEnv
  if let (.const first _, .const second _) := (left.getAppFn, right.getAppFn) then
    if first != second && isStructure env first && isStructure env second then return false
  return true

/-- Assign the unassigned instance metavariables of `e` whose class is known. -/
private def synthesizeInstances (e : Expr) : MetaM Unit := do
  for mvar in ← getMVars e do
    if ← mvar.isAssigned then continue
    let type ← instantiateMVars (← mvar.getType)
    if type.hasExprMVar then continue
    let isInstance ← forallTelescopeReducing type fun _ body => return (← isClass? body).isSome
    unless isInstance do continue
    if let .some value ← trySynthInstance type then mvar.assign value

/-- Unify a binder type with a witness type, except for instance arguments.
Both usually carry open instances (`@MonoidHom ?α ?β ?i ?j`) that only the
goal determines; the caller checks the complete types afterwards. -/
private def unifySkeleton (binderType witnessType : Expr) : MetaM Bool := do
  let binderType ← whnfR binderType
  let witnessType ← whnfR witnessType
  unless ← compatibleStructureHeads binderType witnessType do return false
  if let (.const name _, .const name' _) := (binderType.getAppFn, witnessType.getAppFn) then
    if name == name' && binderType.getAppNumArgs == witnessType.getAppNumArgs then
      let info ← getFunInfo binderType.getAppFn
      for (argument, index) in binderType.getAppArgs.zipIdx do
        let isInstance := (info.paramInfo[index]?.map (·.isInstImplicit)).getD false
        unless isInstance do
          unless ← isDefEq argument witnessType.getAppArgs[index]! do return false
      return true
  isDefEq binderType witnessType

/-- Instantiate the witness's universe parameters and arguments with fresh
metavariables. -/
private def open_ (witness : Witness) : MetaM (Expr × Expr) := do
  let levels ← witness.params.mapM fun _ => mkFreshLevelMVar
  let value := witness.value.instantiateLevelParamsArray witness.params levels
  let type := witness.type.instantiateLevelParamsArray witness.params levels
  let (arguments, _, _) ← forallMetaTelescopeReducing type
  let value := (mkAppN value arguments).headBeta
  return (value, ← instantiateMVars (← inferType value))

/-- The function views of a witness value: its coercion, and that of `symm`
for an equivalence (Mathlib is not imported here, so it is recognized by name). -/
private def functionViews (value type : Expr) : MetaM (Array Expr) := do
  let mut views := #[value]
  if type.isAppOf `Equiv then
    views := views.push (← mkAppM `Equiv.symm #[value])
  views.filterMapM fun view => try coerceToFunction? view catch _ => pure none

/-- The terms a witness provides: the value itself and its function views
applied to a local datum. Each term opens the witness afresh, so the
unification of one candidate cannot constrain another. -/
private def candidates (witness : Witness) (locals : Array Expr) : MetaM (Array Expr) := do
  let (value, type) ← open_ witness
  let mut terms := #[value]
  let viewCount := (← functionViews value type).size
  for index in [:viewCount] do
    for x in locals do
      let saved ← saveState
      let (value, type) ← open_ witness
      let some function := (← functionViews value type)[index]? | saved.restore; continue
      let .forallE _ domain _ _ ← whnfR (← inferType function) | saved.restore; continue
      let localType ← whnfR (← inferType x)
      if ← compatibleStructureHeads domain localType <&&> isDefEq domain localType then
        terms := terms.push (mkApp function x).headBeta
      else saved.restore
  return terms

/-- Propositions of the goal and hypotheses, for open type variables. -/
private def targets (propositions : Array Expr) : Array Expr :=
  propositions.map fun proposition => match proposition.not? with
    | some body => body
    | none => proposition

/-- Whether an argument is an instance. Elaborated hints have their instance
binders abstracted as ordinary ones, so the binder information is not reliable. -/
private def isInstanceArgument (argument : Expr) : MetaM Bool := do
  let type ← instantiateMVars (← inferType argument)
  forallTelescopeReducing type fun _ body => return (← isClass? body).isSome

/-- Assign the instance arguments whose class is determined. -/
private def synthesizeArguments (arguments : Array Expr) : MetaM Unit := do
  for argument in arguments do
    if (← isInstanceArgument argument) && !(← argument.mvarId!.isAssigned) then
      let type ← instantiateMVars (← inferType argument)
      unless type.hasExprMVar do
        if let .some value ← trySynthInstance type then
          argument.mvarId!.assign value

/-- Determine the remaining arguments, matching the conclusion against a target
proposition (the negated goal first) while it is still open, and check that the
witness fits its binder, instances included. Backtracks over the targets. -/
private def complete (arguments : Array Expr) (conclusion : Expr)
    (propositions : Array Expr) (fits : MetaM Bool) : MetaM Bool := do
  let close : MetaM Bool := do
    synthesizeArguments arguments
    -- Also the witness's own instance arguments, e.g. `[∀ i, MulOneClass (f i)]`.
    for argument in arguments do synthesizeInstances (← instantiateMVars argument)
    fits
  synthesizeArguments arguments
  unless (← instantiateMVars conclusion).hasExprMVar do return ← close
  let saved ← saveState
  for target in (targets propositions).reverse do
    if ← isDefEq conclusion target <&&> close then return true
    saved.restore
  -- An open conclusion is still useful to monomorphization.
  close

/-- Close the instantiated premise over its open metavariables. -/
private def abstract (proof type : Expr) (label : String) : MetaM Auto.Lemma := do
  let proof ← instantiateMVars proof
  let type ← instantiateMVars type
  let (proof, s) := Auto.AbstractMVars.abstractExprMVars proof
    { mctx := (← getMCtx), lctx := (← getLCtx), ngen := (← getNGen) }
  let (type, s) := Auto.AbstractMVars.abstractExprMVars type s
  setNGen s.ngen
  setMCtx s.mctx
  -- Open instances stay instance-implicit, so monomorphization synthesizes
  -- them once their types are instantiated.
  let mut lctx := s.lctx
  for x in s.fvars do
    let isInstance ← withLCtx lctx #[] do return (← isClass? (← inferType x)).isSome
    if isInstance then lctx := lctx.setBinderInfo x.fvarId! .instImplicit
  return ⟨⟨lctx.mkLambda s.fvars proof, lctx.mkForall s.fvars type, .leaf label⟩, s.paramNames⟩

private def instancesAssigned (arguments : Array Expr) : MetaM Bool :=
  arguments.allM fun argument => do
    return !(← isInstanceArgument argument) || (← argument.mvarId!.isAssigned)

/-- Whether `type` is a structure other than a class, such as `α ≃ β`. -/
private def isBundled (type : Expr) : MetaM Bool := do
  if ← isProp type then return false
  let .const name _ := (← whnfR type).getAppFn | return false
  let env ← getEnv
  return isStructure env name && !isClass env name

/-- Whether monomorphization cannot determine the type of the binder `argument`:
its type depends on an earlier term argument (`hF : F.FullyFaithful`), or
mentions a type variable that the conclusion determines only through
`argument` (`β` in `Equiv.isEmpty (e : α ≃ β)`, `F` in `⇑g` of `map_sum`).
Ordinary binders such as `(s : Finset α)` are then instantiated by the prover
with the local values of the problem. -/
private def undetermined (argument binderType conclusion : Expr) : MetaM Bool := do
  -- Occurrences in an application of the binder itself (`@DFunLike.coe F M N i g x`)
  -- do not determine it.
  let outside := (← instantiateMVars conclusion).replace fun e =>
    if e.isApp && e.getAppArgs.contains argument then some (mkConst `_) else none
  for mvar in ← getMVars binderType do
    let type ← instantiateMVars (← mvar.getType)
    if (← isClass? type).isSome then continue
    unless (← whnfR type).isSort do return true
    unless (outside.find? (· == .mvar mvar)).isSome do return true
  return false

/-- The premise with `argument := candidate`, closed over its open arguments,
if the candidate fits. -/
private def attempt (argument binderType : Expr) (variableType : Bool) (candidate : Expr)
    (arguments : Array Expr) (conclusion : Expr) (propositions : Array Expr) (proof : Expr)
    (label : String) : MetaM (Option Auto.Lemma) := do
  let candidateType ← inferType candidate
  if variableType && !(← isBundled candidateType) then return none
  -- For a type variable, its classes must hold for the witness.
  let fits := isDefEq binderType candidateType <&&>
    (pure !variableType <||> instancesAssigned arguments)
  unless ← unifySkeleton binderType candidateType do return none
  argument.mvarId!.assign candidate
  unless ← complete arguments conclusion propositions fits do
    trace[vampire] "Data witness {candidate} does not fit {binderType}"
    return none
  let instantiated ← instantiateMVars (mkAppN proof arguments)
  check instantiated
  return some (← abstract instantiated conclusion label)

/-- Premises instantiated at witnesses, see the module comment. -/
def instantiate (premises : Array Auto.Lemma) (witnesses : Array Witness)
    (propositions : Array Expr) : MetaM (Array Auto.Lemma) := do
  unless vampire.dataWitnesses.get (← getOptions) do return #[]
  let budget ← SearchBudget.create (vampire.dataWitnessHeartbeats.get (← getOptions))
  let some (locals, localWitnesses) ← budget.run (do
    let locals ← (← getLCtx).getFVars.filterM fun x => do
      let decl ← x.fvarId!.getDecl
      if decl.isImplementationDetail then return false
      isBundled (← inferType x)
    let locals := locals.extract 0 maxLocals
    let localWitnesses ← locals.mapM fun x => do
      return { value := x, type := ← inferType x, params := #[], label := toString x,
               isLocal := true : Witness }
    return (locals, localWitnesses)) | return #[]
  let witnesses := witnesses ++ localWitnesses
  if witnesses.isEmpty then return #[]
  trace[vampire] "Data witnesses: {witnesses.map (·.label)}"
  let mut found := #[]
  let mut seen : Std.HashSet Expr := {}
  for premise in premises do
    let some arity ← budget.run (forallTelescopeReducing premise.type fun xs _ => pure xs.size)
      | return found
    for index in [:arity] do
      for witness in witnesses do
        if found.size >= maxFacts then return found
        if ← budget.exhausted then return found
        let some facts ← budget.run (withNewMCtxDepth do
          let levels ← premise.params.mapM fun _ => mkFreshLevelMVar
          let proof := premise.proof.instantiateLevelParamsArray premise.params levels
          let type := premise.type.instantiateLevelParamsArray premise.params levels
          let (arguments, kinds, conclusion) ← forallMetaTelescopeReducing type
          let some argument := arguments[index]? | return #[]
          unless kinds[index]! == .default do return #[]
          let binderType ← instantiateMVars (← inferType argument)
          -- Only bundled objects (`α ≃ β`, `M →* N`, `F.FullyFaithful`):
          -- ordinary variables are instantiated by monomorphization and the
          -- prover, and classes by instance synthesis. A binder `g : F` of a
          -- type variable stands for a bundled object when classes such as
          -- `AddMonoidHomClass F M N` constrain `F` (`map_sum`, `map_prod`).
          let variableType := binderType.isMVar
          unless variableType || (← isBundled binderType) do return #[]
          -- A local value is a term of the problem: the prover instantiates a
          -- binder with it once monomorphization has determined its type.
          if witness.isLocal && !(← undetermined argument binderType conclusion) then return #[]
          let mut facts := #[]
          for candidate in ← (try candidates witness locals catch _ => pure #[]) do
            let saved ← saveState
            let label := s!"{labelPrefix}{witness.label} in {premise.deriv}"
            let fact? ← tryCatchRuntimeEx
              (attempt argument binderType variableType candidate arguments conclusion
                propositions proof label)
              fun error => do
                if error.isInterrupt || error.isRuntime then throw error
                trace[vampire] "Data witness {witness.label} does not fit {premise.deriv}: {error.toMessageData}"
                pure none
            if let some fact := fact? then facts := facts.push fact
            saved.restore
          return facts) | do
            if ← budget.exhausted then return found
            continue
        for fact in facts do
          unless seen.contains fact.type do
            seen := seen.insert fact.type
            trace[vampire] "Instantiated a premise at a data witness: {fact.type}"
            found := found.push fact
  return found

end VampireHammer.Export.DataWitnesses

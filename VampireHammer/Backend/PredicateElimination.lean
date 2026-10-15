import VampireHammer.Backend.Instantiation
import VampireHammer.Backend.EUF

/-! Recover the finite hyperresolution instance omitted by Vampire's predicate
elimination annotation. Search proposes instances; EUF checks their consequence.
Repeated satellites receive independent, typed instantiations. -/
namespace VampireHammer.Backend
open Lean Meta
open VampireHammer.ClauseMeta Internal

structure OpenClause where
  clause : GroundClause
  variables : Array Expr

def openClauseParent (parent : ParentProof) : MetaM (Option OpenClause) := do
  let mut proof := parent.proof
  let mut variables := #[]
  for _ in parent.binders do
    let type ← whnf (← inferType proof)
    unless type.isForall do return none
    let value ← mkFreshExprMVar type.bindingDomain!
    variables := variables.push value
    proof := mkApp proof value
  let some clause ← groundClause proof (← inferType proof) | return none
  pure (some ⟨clause, variables⟩)

private def signedAtom (literal : Expr) : MetaM (Bool × Expr) := do
  if let some atom ← notArgument? literal then return (false, atom)
  pure (true, literal)

private def isPredicate (atom : Expr) : Bool :=
  !atom.isAppOf ``Eq && !atom.isConstOf ``True && !atom.isConstOf ``False

/-- Equality-mode elimination can leave nonunifiable argument disequalities.
Unify solvable argument positions, retaining the others for the EUF checker. -/
private partial def reconcile (left right : Expr) : MetaM Unit := do
  if ← withoutModifyingState (isDefEq left right) then
    discard <| isDefEq left right
  else
    let left ← instantiateMVars left
    let right ← instantiateMVars right
    match left, right with
    | .app lf la, .app rf ra =>
      if ← withoutModifyingState (isDefEq lf rf) then reconcile la ra
    | _, _ => pure ()

partial def matchClauseLiterals (literals : List Expr) (target : Array Expr)
    (budget : IO.Ref Nat) (finish : MetaM (Option Expr)) : MetaM (Option Expr) := do
  match literals with
  | [] => finish
  | literal :: rest =>
    for candidate in target do
      let remaining ← budget.get
      if remaining == 0 then return none
      budget.set (remaining - 1)
      let saved ← saveState
      if (← literalEquivalent? literal candidate).isSome then
        if let some result ← matchClauseLiterals rest target budget finish then return some result
      saved.restore
    pure none

private def finishVariables (variables : Array Expr) : MetaM Bool := do
  for v in variables do
    let value ← instantiateMVars v
    if value.isMVar then
      let domain ← inferType value
      let mut representative? := none
      for decl in ← getLCtx do
        unless decl.isImplementationDetail do
          if ← isDefEq decl.type domain then
            representative? := some decl.toExpr
            break
      let some representative := representative? | return false
      value.mvarId!.assign representative
  pure true

def closeClauseInstances (clauses : Array OpenClause) : MetaM (Option (Array GroundClause)) := do
  unless ← finishVariables (clauses.flatMap (·.variables)) do return none
  let closed ← clauses.mapM fun clause => do
    let proof ← instantiateMVars clause.clause.proof
    if proof.hasExprMVar then return none
    groundClause proof (← inferType proof)
  pure (closed.mapM id)

private partial def recoverSatellites (input : RuleInput) (nucleusParent : ParentProof)
    (predicate : Expr) (polarity : Bool) (pivots target : Array Expr) (attempts : IO.Ref Nat)
    (fuel index : Nat) (clauses : Array OpenClause) : MetaM (Option Expr) := do
  if fuel = 0 then return none
  if index >= pivots.size then
    let some closed ← closeClauseInstances clauses | return none
    return ← eufConsequence closed target
  let remaining ← attempts.get
  if remaining == 0 then return none
  attempts.set (remaining - 1)
  for parent in input.parents do
    if parent.parent.name == nucleusParent.parent.name then continue
    let branchState ← saveState
    let some satellite ← openClauseParent parent | branchState.restore; continue
    let mut selected := #[]
    let mut tail := #[]
    for literal in satellite.clause.literals do
      let (sign, literalAtom) ← signedAtom literal
      if sign != polarity && literalAtom.getAppFn == predicate then
        selected := selected.push literalAtom
      else tail := tail.push literal
    if selected.size == 1 then
      -- Reconcile each first-order argument independently.
      let leftArgs := pivots[index]!.getAppArgs
      let rightArgs := selected[0]!.getAppArgs
      if leftArgs.size == rightArgs.size then
        for (left, right) in leftArgs.zip rightArgs do reconcile left right
        if let some proof ← matchClauseLiterals tail.toList target attempts
            (recoverSatellites input nucleusParent predicate polarity pivots target attempts (fuel - 1) (index + 1) (clauses.push satellite)) then return some proof
    branchState.restore
  pure none

/-- Binary elimination and multi-occurrence hyperresolution, with shared
satellites instantiated separately for each occurrence of the eliminated atom. -/
def predicateElimination (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size >= 2 &&
      input.parents.all (·.clauseForm) do return none
  let attempts ← IO.mkRef (4096 : Nat)
  underConclusionBinders input fun bindings _ => do
    let some target := targetClauseLiterals? input bindings | return none
    for nucleusParent in input.parents do
      let saved ← saveState
      let some nucleus ← openClauseParent nucleusParent | saved.restore; continue
      for pivot in nucleus.clause.literals do
        let pivotState ← saveState
        let (polarity, atom) ← signedAtom pivot
        unless isPredicate atom do continue
        let predicate := atom.getAppFn
        let mut pivots := #[]
        let mut remainder := #[]
        for literal in nucleus.clause.literals do
          let (sign, literalAtom) ← signedAtom literal
          if sign == polarity && literalAtom.getAppFn == predicate then
            pivots := pivots.push literalAtom
          else remainder := remainder.push literal
        -- Elimination removes this predicate entirely from the resolvent.
        let mut survives := false
        for literal in target do
          if (← signedAtom literal).2.getAppFn == predicate then survives := true
        if survives then continue
        if let some proof ← matchClauseLiterals remainder.toList target attempts (recoverSatellites input nucleusParent predicate polarity pivots target attempts (pivots.size + 1) 0 #[nucleus]) then
          return some proof
        pivotState.restore
      saved.restore
    pure none

end VampireHammer.Backend

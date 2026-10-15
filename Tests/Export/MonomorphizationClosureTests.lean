import VampireHammer.Export.Monomorphization

open Lean Meta Elab Tactic VampireHammer.Export.Internal

elab "close_temporary_proof" : tactic => withMainContext do
  let goal ← getMainGoal
  let original ← getLCtx
  let nat := mkConst ``Nat
  let zero := mkNatLit 0
  let proof ← withLetDecl `temporaryType (mkSort (.succ .zero)) nat fun type =>
    withLetDecl `temporaryValue type zero fun value => do
      withLetDecl `temporaryProof (← mkEq value value)
          (mkApp2 (mkConst ``Eq.refl [.succ .zero]) type value) fun proof =>
        closeMonomorphizationProof original proof
  unless (collectFVars {} proof).fvarIds.all original.contains do
    throwError "temporary proof depends on an expired context"
  goal.assign proof

-- Both the proof and its type depend on nested temporary definitions.
example : (0 : Nat) = 0 := by close_temporary_proof

elab "check_context_closure" : tactic => withMainContext do
  let nat := mkConst ``Nat
  withLetDecl `callerValue nat (mkNatLit 0) fun callerValue => do
    let original ← getLCtx
    withLetDecl `temporaryAlias nat callerValue fun alias => do
      let closed ← closeMonomorphizationProof original alias
      unless closed == callerValue do
        throwError "closure unnecessarily unfolded the caller's definition"
    withLocalDeclD `unboundTemporary nat fun temporary => do
      let rejected ← try
        let _ ← closeMonomorphizationProof original temporary
        pure false
      catch _ => pure true
      unless rejected do throwError "an unbound temporary assumption escaped"

example : True := by
  check_context_closure
  trivial

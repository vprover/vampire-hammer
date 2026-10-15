import VampireHammer.Backend.Congruence

open Lean Meta Elab Tactic VampireHammer.Backend.Internal

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private def proveCongruence : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (_, left, right) := (← goal.getType).eq? | throwError "expected equality"
  let equality ← lookup "h"
  let some (_, u, v) := (← inferType equality).eq? | throwError "expected hypothesis equality"
  let some proof ← congruenceWithEquations #[(equality, u, v)] left right
    | throwError "higher-order congruence declined"
  unless ← isTypeCorrect proof do throwError "ill-typed congruence proof"
  goal.assign proof

theorem congruence_beneath_lambda (f g k : Nat → Nat) (h : f = g) :
    (fun x => k (f x)) = (fun x => k (g x)) := by
  run_tac proveCongruence

theorem congruence_nested_lambdas (f g : Nat → Nat → Nat) (h : f = g) :
    (fun x y => f y (x + y)) = (fun x y => g y (x + y)) := by
  run_tac proveCongruence

theorem congruence_beneath_forall (P Q : Nat → Prop) (h : P = Q) :
    (∀ x, P (x + 1)) = (∀ x, Q (x + 1)) := by
  run_tac proveCongruence

example (f g : Nat → Nat) (h : f = g) : True := by
  run_tac withMainContext do
    let f ← lookup "f"
    let g ← lookup "g"
    let proof ← lookup "h"
    let left ← withLocalDeclD `x (mkConst ``Nat) fun x => mkLambdaFVars #[x] (mkApp f x)
    let right ← withLocalDeclD `x (mkConst ``Nat) fun x =>
      mkLambdaFVars #[x] (mkApp (mkConst ``Nat.succ) (mkApp g x))
    if (← congruenceWithEquations #[(proof, f, g)] left right).isSome then
      throwError "accepted an unrelated lambda body"
  trivial

#print axioms congruence_beneath_lambda
#print axioms congruence_nested_lambdas
#print axioms congruence_beneath_forall

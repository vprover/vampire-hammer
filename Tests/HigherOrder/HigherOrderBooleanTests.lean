import VampireHammer.Backend.HigherOrderBoolean

open Lean Meta Elab Tactic VampireHammer.Backend

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private def inputFor (target : Expr) : MetaM RuleInput := do
  let proof ← lookup "h"
  pure {
    step := {
      name := "boolean"
      formula := .base .trueE
      binders := #[]
      parents := #[{ name := "parent" }]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    clauseLiterals? := none
    parents := #[{
      parent := { name := "parent" }
      binders := #[]
      existentialVariables := #[]
      componentBinders := #[]
      target := ← inferType proof
      clauseForm := false
      clauseLiterals? := none
      cnfCandidates := pure none
      proof }]
    sourceProof? := none
    sourceFVars := #[]
    symbols := {} }

private def replayBoolean : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let input ← inputFor (← goal.getType)
  let some proof ← higherOrderBoolean input | throwError "Boolean inference declined"
  unless ← isTypeCorrect proof do throwError "ill-typed Boolean inference"
  goal.assign proof

theorem boolean_equality_left (A p q : Prop) (h : A ∨ p = q) : A ∨ (¬p) ≠ q := by
  run_tac replayBoolean

theorem boolean_equality_right (p q : Prop) (h : p = q) : p ≠ (¬q) := by
  run_tac replayBoolean

theorem boolean_simp_under_lambda (Q : (Nat → Prop) → Prop) (p : Nat → Prop)
    (h : Q (fun x => (p x ∧ True) ∨ False)) : Q p := by
  run_tac replayBoolean

theorem boolean_simp_complement (Q : Prop → Prop) (p : Prop)
    (h : Q (p ∧ ¬p)) : Q False := by
  run_tac replayBoolean

theorem boolean_and_proxy (A p q : Prop) (h : A ∨ ((p ∧ q) = True)) :
    p = True ∨ A := by
  run_tac replayBoolean

theorem boolean_negative_and_proxy (A p q : Prop) (h : A ∨ ((p ∧ q) = False)) :
    p = False ∨ A ∨ q = False := by
  run_tac replayBoolean

theorem boolean_or_proxy (A p q : Prop) (h : A ∨ ((p ∨ q) = True)) :
    p = True ∨ A ∨ q = True := by
  run_tac replayBoolean

theorem boolean_imp_proxy (A p q : Prop) (h : A ∨ ((p → q) = True)) :
    p = False ∨ A ∨ q = True := by
  run_tac replayBoolean

theorem boolean_iff_proxy (A p q : Prop) (h : A ∨ ((p ↔ q) = True)) :
    A ∨ p = q := by
  run_tac replayBoolean

theorem boolean_equality_proxy (A : Prop) (x y : Nat) (h : A ∨ ((x = y) = False)) :
    A ∨ x ≠ y := by
  run_tac replayBoolean

theorem boolean_proxy_quantified (A P Q : Nat → Prop)
    (h : ∀ x, A x ∨ ((P x ∧ Q x) = True)) : ∀ x, P x = True ∨ A x := by
  run_tac replayBoolean

theorem boolean_proxy_quantified_prop (A : Prop) (Q : Prop → Prop)
    (h : ∀ p, A ∨ ((Q p ∧ p) = True)) : ∀ p, Q p = True ∨ A := by
  run_tac replayBoolean

theorem boolean_forall_reordering (P : Nat → Nat → Prop) (h : ∀ x y, P x y) :
    ∀ y x, P x y := by
  run_tac replayBoolean

example (A p q : Prop) (h : A ∨ ((p ∧ q) = True)) : True := by
  run_tac withMainContext do
    let input ← inputFor (← mkAppM ``Eq #[← lookup "p", mkConst ``True])
    if (← higherOrderBoolean input).isSome then throwError "dropped the clause context"
  trivial

example (p q : Prop) (h : p = q) : True := by
  run_tac withMainContext do
    let input ← inputFor (← mkAppM ``Not #[← mkEq (← lookup "p") (← lookup "q")])
    if (← higherOrderBoolean input).isSome then throwError "flipped equality polarity"
  trivial

#print axioms boolean_simp_under_lambda
#print axioms boolean_and_proxy
#print axioms boolean_equality_left

example (A p : Prop) (h : A ∧ p) : True := by
  run_tac withMainContext do
    if (← higherOrderBooleanEquivalent (← lookup "h") (← lookup "A")).isSome then
      throwError "input boundary accepted a weaker proposition"
  trivial

example (h : False) : True := by
  run_tac withMainContext do
    if (← higherOrderBooleanEquivalent (← lookup "h") (mkConst ``True)).isSome then
      throwError "input boundary confused False and True"
  trivial

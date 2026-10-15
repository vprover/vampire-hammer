import VampireHammer.Backend_Structural

open Lean Meta Elab Tactic

elab "transport_formula " source:term : tactic => withMainContext do
  let goal ← getMainGoal
  let proof ← Term.elabTerm source none
  let some transported ← VampireHammer.Structural.transport proof (← goal.getType)
    | throwError "structural transport declined"
  goal.assign transported

example (P Q : Prop) (h : P = Q) : P ↔ Q := by
  transport_formula h

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  transport_formula h

example (P Q : Prop) (h : ¬(P = Q)) : ¬(P ↔ Q) := by
  transport_formula h

example (P Q : Prop) (h : ¬(P ↔ Q)) : ¬(P = Q) := by
  transport_formula h

example {α : Type} (P Q : α → Prop) (R : Prop)
    (h : ∀ x, P x = Q x ∧ R) : ∀ x, (P x ↔ Q x) ∧ R := by
  transport_formula h

example {α : Type} (P Q : α → Prop) (R : Prop)
    (h : ∃ x, R ∧ (P x ↔ Q x)) : ∃ x, R ∧ P x = Q x := by
  transport_formula h

-- Equality of ordinary data must remain equality, and unrelated propositions
-- must not become equivalent just because the conversion is available.
example (a b : Nat) (h : a = b) : a = b := by
  transport_formula h

example (P Q R : Prop) (h : P = Q) : P = Q := by
  fail_if_success have : P ↔ R := by transport_formula h
  transport_formula h

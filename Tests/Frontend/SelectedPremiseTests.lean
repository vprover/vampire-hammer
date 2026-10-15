import VampireHammer

-- These checks must close without an external solver.
set_option vampire.executable "/missing-vampire-selected-premise-tests"
set_option vampire.attributeLemmas false

namespace SelectedPremiseTests

opaque Target (P : Prop) : Prop
axiom conclusion (P : Prop) : P → Target P

theorem exact_selected_premise (P : Prop) (h : P) : Target P := by
  vampire [conclusion, h]

example (P : Prop) (h : P) : Target P := by
  fail_if_success vampire [conclusion]
  exact conclusion P h

-- Hypotheses introduced from the goal remain eligible, even without '*'.
theorem introduced_premise (P : Prop) : P → Target P := by
  vampire [conclusion]

theorem bool_left_clash : ¬(true = false) := by vampire []
theorem bool_right_clash : ¬(false = true) := by vampire []

theorem option_clash {α : Type u} (a : α) : ¬(some a = none) := by vampire []
theorem option_clash_equivalence {α : Type u} (a : α) : (some a = none) ↔ False := by
  vampire []

example (h : true = false) : False := by
  fail_if_success vampire []
  vampire [h]

#print axioms exact_selected_premise
#print axioms introduced_premise
#print axioms bool_left_clash
#print axioms option_clash_equivalence

end SelectedPremiseTests

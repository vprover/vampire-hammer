import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 10

/-! A local order instance defined by a formula. `≤` stays a TF0 symbol; its
definition is exported as `∀ a b, a ≤ b ↔ …`, and the constructors occurring
there contribute distinctness laws. -/

inductive Val where
  | Low | High | X | Z

namespace Val

instance : LE Val where
  le a b := a = b ∨ a = .Low ∨ b = .High

instance : LT Val where
  lt a b := a ≤ b ∧ ¬ b ≤ a

set_option vampire.outputPath "artifacts/instance-definition-refl.p" in
theorem le_refl' (a : Val) : a ≤ a := by vampire

set_option vampire.outputPath "artifacts/instance-definition-trans.p" in
theorem le_trans' (a b c : Val) : a ≤ b → b ≤ c → a ≤ c := by vampire

set_option vampire.outputPath "artifacts/instance-definition-antisymm.p" in
theorem le_antisymm' (a b : Val) : a ≤ b → b ≤ a → a = b := by vampire

-- `<` is defined through `≤`; both definitions are added.
set_option vampire.outputPath "artifacts/instance-definition-lt.p" in
theorem low_lt_x : Val.Low < Val.X := by vampire

#print axioms le_trans'

end Val

/-! Without the definition `≤` is an uninterpreted predicate, and the problem
is satisfiable. (Definition alignment would open the inline `≤` of the goal by
itself.) -/

set_option vampire.outputPath "artifacts/instance-definition-off.p" in
example (a : Val) : a ≤ a := by
  fail_if_success vampire (instanceDefinitions := false) (unfoldingPlan := false)
    (alignInstantiatedDefinitions := false)
  exact Or.inl rfl

import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-applied-variable-resolution.sh"
set_option vampire.outputPath "artifacts/applied-variable-resolution.p"
set_option trace.vampire.replay true

/-- The unifier values here are `X0 ↦ g(Y0)`.  This checks the recursive
translation and later materialization of a term containing a target variable. -/
theorem appliedVariableResolution {α : Type} (g : α → α) (P Q R S T : α → Prop)
    (hPositive : ∀ x, P x ∨ Q x ∨ R x)
    (hNegative : ∀ x, ¬ P x ∨ S x ∨ T x) :
    ∀ y, Q (g y) ∨ R (g y) ∨ S (g y) ∨ T (g y) := by
  vampire [hPositive, hNegative]

#print axioms appliedVariableResolution

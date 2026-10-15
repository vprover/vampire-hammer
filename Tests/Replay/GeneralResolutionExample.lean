import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-general-variable-resolution.sh"
set_option vampire.outputPath "artifacts/general-variable-resolution.p"
set_option trace.vampire.replay true

/-- A mock Vampire proof resolves `P x ∨ Q x ∨ R x` with
`¬ P x ∨ S x ∨ T x`.  Its unifier explicitly maps each parent `X0` to the
resolvent variable `Y0`, and the direct backend builds `Q y ∨ R y ∨ S y ∨ T y`.
-/
theorem generalVariableResolution {α : Type} (P Q R S T : α → Prop)
    (hPositive : ∀ x, P x ∨ Q x ∨ R x)
    (hNegative : ∀ x, ¬ P x ∨ S x ∨ T x) :
    ∀ y, Q y ∨ R y ∨ S y ∨ T y := by
  vampire [hPositive, hNegative]

#print axioms generalVariableResolution

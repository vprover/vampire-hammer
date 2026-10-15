import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-equality-resolution.sh"
set_option vampire.outputPath "artifacts/equality-resolution-example.p"
set_option trace.vampire.replay true

/-- Equality resolution applies `X ↦ a`, removes the resulting false literal
`a ≠ a`, and leaves `P a`. -/
theorem equalityResolutionExample {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire [parent, notP]

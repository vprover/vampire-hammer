import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/real-equality-factoring.sh"
set_option vampire.outputPath "artifacts/real-equality-factoring-example.p"
set_option trace.vampire.replay true

/-- This test invokes the real modified Vampire binary. Equality factoring
applies `Y ↦ X`, removes `f X = a`, and derives
`a ≠ b ∨ f X = b ∨ R X`. -/
theorem realEqualityFactoringExample {α : Type} (f : α → α) (d a b : α)
    (R : α → Prop)
    (S : α → α → Prop)
    (parent : ∀ x y, f x = a ∨ f y = b ∨ R y)
    (notSOrEq : ¬ S a b ∨ a = b) (hasS : S a b)
    (notFb : f d ≠ b) (notR : ¬ R d) : False := by
  vampire [parent, notSOrEq, hasS, notFb, notR]

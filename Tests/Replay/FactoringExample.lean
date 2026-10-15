import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true
set_option vampire.outputPath "artifacts/factoring-example.p"
set_option trace.vampire.replay true

/-- Vampire's factoring certificate removes the second occurrence from
`P x ∨ P y` after its mgu makes the two literals equal. -/
theorem factoringExample {α : Type} (a : α) (P : α → Prop)
    (h : ∀ x y, P x ∨ P y) : P a := by
  vampire [h]

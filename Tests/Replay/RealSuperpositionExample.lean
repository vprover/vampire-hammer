import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true
set_option vampire.outputPath "artifacts/real-superposition-example.p"
set_option trace.vampire.replay true

/-- A real Vampire run that uses a positive unit equality right-to-left. -/
theorem realSuperpositionExample {α : Type} (a b : α) (P : α → Prop) (Q R : Prop)
    (hEq : a = b ∨ Q) (hNotQ : ¬ Q) (hP : P a) (hNotP : ¬ P b) : R := by
  vampire [hEq, hNotQ, hP, hNotP]

import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-superposition-all-occurrences.sh"
set_option vampire.outputPath "artifacts/superposition-all-occurrences.p"
set_option trace.vampire.replay true

/-- The mock proof's f12 is a ground superposition step whose equality parent
is the non-unit clause `Q ∨ a = b`. Its rewritten literal is `¬ Pair b b`, so
reconstruction must produce `¬ Pair a a ∨ Q`: both term occurrences change,
the unused equality-parent literal is retained, and the equality itself is at
position one. -/
theorem superpositionRewritesAllOccurrences {α : Type} (a b : α)
    (Pair : α → α → Prop) (Q : Prop)
    (hEq : a = b ∨ Q) (hNotQ : ¬ Q)
    (hPair : Pair a a) (hNotPair : ¬ Pair b b) : False := by
  vampire [hEq, hNotQ, hPair, hNotPair]

import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-nested-a-clause.sh"
set_option vampire.outputPath "artifacts/nested-a-clause.p"

/-- Regression test for Vampire's native quantified A-clause surface form.

The mock's `f3` is written as `(! [X] : P(X)) | ~spl0_1`.  The parser-side
preparation is the identity, so this reaches `Replay` unchanged.  Replay must
recover the binder from the regular disjunct and store the result as a
quantified `Clause.AClause.Holds` proof. -/
theorem nestedAClauseExample {α : Type} (P : α → Prop) (a : α)
    (notP : ¬ (P a ∨ ¬ True)) (allP : ∀ x, P x) : False := by
  vampire [notP, allP]

#print axioms nestedAClauseExample

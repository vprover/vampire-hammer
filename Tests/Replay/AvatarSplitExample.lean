import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-avatar-split-negative.sh"
set_option vampire.outputPath "artifacts/avatar-split-negative.p"
set_option trace.vampire.replay true

/-- Regression test for `avatar_split_clause` when every split atom occurs
negatively. The clause order is reversed, as in the paper-style ground example.
The mock proof also exercises the parser and AVATAR's SAT boundary. -/
theorem avatarSplitNegativeExample (A B C D : Prop)
    (h : ¬ A ∨ ¬ B ∨ ¬ C ∨ ¬ D)
    (hA : A) (hB : B) (hC : C) (hD : D) : False := by
  vampire [h, hA, hB, hC, hD]

#print axioms avatarSplitNegativeExample

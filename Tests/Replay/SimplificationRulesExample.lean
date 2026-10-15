import VampireHammer

/-!
End-to-end tests for the certificate-free rules in `Backend.Simplification`:
`true_and_false_elimination`, `closure`, `reorient_equations`, and
`consistent_polarity_flipping`. The mock proofs make the test deterministic while exercising the parser, decoder,
local proof DAG, and Lam2DAAF boundary.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-simplification-rules.sh"
set_option vampire.outputPath "artifacts/simplification-rules.p"
set_option trace.vampire.replay true

/-- The mock refutation removes `True`/`False` from `hTrue`, closes `hAll`
over its variables in the other order, and swaps the sides of `hEq`. -/
theorem simplificationRules {α : Type} (a : α) (f : α → α) (P : α → α → Prop) (A : Prop)
    (hTrue : (A ∧ True) ∨ False) (hAll : ∀ x y, P x y) (hEq : A → f a = a)
    (hGoal : ¬P a a ∨ a ≠ f a) : False := by
  vampire [hTrue, hAll, hEq, hGoal]

#print axioms simplificationRules

set_option vampire.executable "Tests/testdata/scripts/mock-polarity-flipping.sh"
set_option vampire.outputPath "artifacts/polarity-flipping.p"

/-- The mock refutation flips the polarity of `P` after clausification and
then resolves the flipped clauses. Replay reads `P` in those clauses as
`fun x => ¬ P x`. -/
theorem polarityFlipping {α : Type} (a : α) (P : α → Prop) (Q : Prop)
    (hAll : ∀ x, P x) (hImp : ¬P a ∨ Q) (hNot : ¬Q) : False := by
  vampire [hAll, hImp, hNot]

#print axioms polarityFlipping

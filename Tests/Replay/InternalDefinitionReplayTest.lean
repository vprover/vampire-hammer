import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-internal-definition-unfolding.sh"
set_option vampire.outputPath "artifacts/internal-definition-unfolding.p"
set_option trace.vampire.replay true

/-! Every single-parent unfolding is used in the final refutation. Sources
already contain the wrappers, so this also tests their interpretation against
the actual exported Lean hypotheses, not just the rule's local proof. -/
theorem internalDefinitionReplay {α : Type} (f : α → α) (a : α) (P : α → Prop)
    (hEq : ∀ x, f (f x) = f x) (hNe : ∀ x, f (f x) ≠ f x ∨ P x)
    (hNot : ¬P a) : False := by
  vampire [hEq, hNe, hNot]

#print axioms internalDefinitionReplay

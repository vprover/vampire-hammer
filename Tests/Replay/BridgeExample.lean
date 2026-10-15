import VampireHammer

-- Keep checking in Lean's reduction-based mode for this proof experiment.
set_option auto.checker.buildMode "indirectReduce"

theorem bridgeExample {α : Type} (a : α) (P Q : α → Prop)
    (h₁ : ∀ x, P x → Q x) (h₂ : P a) : Q a := by
  vampire_bridge [h₁, h₂]

-- Exercise premise ordering, universe parameters and irrelevant hypotheses.
theorem bridgeReordered {α : Type u} (a : α) (P Q : α → Prop) (R : Prop)
    (_unused : R) (pa : P a) (step : ∀ x, P x → Q x) : Q a := by
  vampire_bridge [pa, _unused, step]

-- The backend must not use an unselected proof from the original context.
theorem bridgeMissingPremise {α : Type} (a : α) (P Q : α → Prop)
    (step : ∀ x, P x → Q x) (pa : P a) : Q a := by
  fail_if_success vampire_bridge [step]
  exact step a pa

#print axioms bridgeExample
#print axioms bridgeReordered

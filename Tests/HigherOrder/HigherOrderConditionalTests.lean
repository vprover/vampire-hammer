import VampireHammer

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5

-- Native HO exports a conditional as t_ite0. Its local interpretation must
-- remain the checked Lean conditional, rather than a fresh uninterpreted head.
theorem conditional_replay {α : Type} (p : Prop) [Decidable p]
    (a b : α) (P : α → Prop) (ha : P (if p then a else b))
    (negative : ∀ x, ¬P x) : False := by
  vampire [ha, negative]

-- Exercise a second conditional sort in the same signature.
theorem two_conditional_sorts {α β : Type} (p : Prop) [Decidable p]
    (a b : α) (c d : β) (R : α → β → Prop)
    (hac : R (if p then a else b) (if p then c else d))
    (negative : ∀ x y, ¬R x y) : False := by
  vampire [hac, negative]

-- The selected branch matters: accepting conditionals must not erase their
-- condition, reverse branches, or infer an unselected premise.
example {α : Type} (p : Prop) [Decidable p] (a b : α) (P : α → Prop)
    (hp : ¬p) (ha : P a) : True := by
  fail_if_success have : P (if p then a else b) := by vampire [hp, ha]
  trivial

#print axioms conditional_replay
#print axioms two_conditional_sorts

import VampireHammer

set_option vampire.higherOrder false
set_option vampire.higherOrderFallback false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5
set_option vampire.outputPath "artifacts/fool-conditional.p"

-- These require the conditional's branch meaning, rather than merely its type.
theorem fool_true_branch {α : Type} (p : Prop) [Decidable p]
    (a b : α) (P : α → Prop) (hp : p) (ha : P a) :
    P (if p then a else b) := by
  vampire [hp, ha]

theorem fool_false_branch {α : Type} (p : Prop) [Decidable p]
    (a b : α) (P : α → Prop) (hp : ¬p) (hb : P b) :
    P (if p then a else b) := by
  vampire [hp, hb]

theorem fool_quantified_branch {α : Type} (p : α → Prop) [∀ x, Decidable (p x)]
    (f g : α → α) (P : α → Prop) (h : ∀ x, p x ∧ P (f x)) :
    ∀ x, P (if p x then f x else g x) := by
  vampire [h]

-- Function branches exercise the first-order object encoding as well.
theorem fool_function_branch (p : Prop) [Decidable p] (f g : Nat → Nat)
    (R : (Nat → Nat) → Prop) (hp : p) (hf : R f) :
    R (if p then f else g) := by
  vampire [hp, hf]

-- The conditional in this source remains below a quantifier. Vampire must
-- introduce a fresh function, with separate universal branch definitions.
theorem fool_quantified_definition {α : Type} (p : α → Prop) [∀ x, Decidable (p x)]
    (f g : α → α) (P : α → Prop) (h : ∀ x, P (if p x then f x else g x))
    (hp : ∀ x, p x) : ∀ x, P (f x) := by
  vampire [h, hp]

theorem fool_nested_branch {α : Type} (p q : Prop) [Decidable p] [Decidable q]
    (a b c : α) (P : α → Prop) (hp : p) (hq : ¬q) (hb : P b) :
    P (if p then (if q then a else b) else c) := by
  vampire [hp, hq, hb]

example {α : Type} (p : Prop) [Decidable p] (a b : α) (P : α → Prop)
    (hp : ¬p) (ha : P a) : True := by
  fail_if_success have : P (if p then a else b) := by vampire [hp, ha]
  trivial

#print axioms fool_true_branch
#print axioms fool_false_branch
#print axioms fool_quantified_branch
#print axioms fool_function_branch
#print axioms fool_quantified_definition
#print axioms fool_nested_branch

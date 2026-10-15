import VampireHammer

set_option vampire.executable "/missing-vampire-constructor-equivalence"

structure CheckedWitness {α : Type u} (P : α → Prop) where
  value : α
  property : P value

-- Dependent proof fields cannot be abstracted as independent first-order
-- arguments. Checked no-confusion and substitution handle them before export.
theorem dependent_constructor_equivalence {α : Type u} (P : α → Prop)
    (a b : α) (ha : P a) (hb : P b) :
    (CheckedWitness.mk a ha = CheckedWitness.mk b hb) = (a = b) := by
  vampire []

theorem reversed_constructor_equivalence {α : Type u} (P : α → Prop)
    (a b : α) (ha : P a) (hb : P b) :
    (a = b) ↔ (CheckedWitness.mk a ha = CheckedWitness.mk b hb) := by
  vampire []

-- Closing the forward direction must use only the equations obtained from
-- injection, never unrelated unselected hypotheses from the caller's context.
example {α : Type u} (P : α → Prop) (a b : α) (ha : P a) (hb : P b)
    (Q : Prop) (q : Q) (equal : a = b) : True := by
  fail_if_success have : (CheckedWitness.mk a ha = CheckedWitness.mk b hb) ↔ Q := by vampire []
  trivial

#print axioms dependent_constructor_equivalence
#print axioms reversed_constructor_equivalence

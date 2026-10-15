import VampireHammer
import Mathlib.Data.Set.Basic

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.attributeLemmas false

-- No Nonempty assumptions: funext supplies an element in each pointwise goal.
set_option vampire.outputPath "artifacts/function-equality-simple.p" in
theorem function_equality_simple {α β : Type} (f g : α → β)
    (pointwise : ∀ x, f x = g x) : f = g := by
  vampire [pointwise]

set_option vampire.outputPath "artifacts/function-equality-curried.p" in
theorem function_equality_curried {α β γ : Type} (f g : α → β → γ)
    (pointwise : ∀ x y, f x y = g x y) : f = g := by
  vampire [pointwise]

set_option vampire.outputPath "artifacts/function-equality-dependent.p" in
theorem function_equality_dependent {α : Type} {β : α → Type} (f g : ∀ x, β x)
    (pointwise : ∀ x, f x = g x) : f = g := by
  vampire [pointwise]

set_option vampire.outputPath "artifacts/function-equality-set.p" in
theorem function_equality_set {α : Type} (a b c : Set α) :
    (a ∩ b) \ c = a ∩ (b \ c) := by
  vampire []

-- Neither fact alone proves the pointwise goal: Vampire must combine them.
set_option vampire.outputPath "artifacts/function-equality-transitive.p" in
theorem function_equality_transitive {α β : Type} (f g h : α → β)
    (left : ∀ x, f x = g x) (right : ∀ x, g x = h x) : f = h := by
  vampire [left, right]

-- A failed application must restore its assignments before trying the next fact.
theorem function_equality_application_rollback {α : Type} {β : α → Type}
    (f g : ∀ x, β x) (unusable : ∀ x, False → f x = g x)
    (pointwise : ∀ x, f x = g x) : f = g := by
  vampire [unusable, pointwise]

-- Explicit fact selection must also apply to the direct application step.
example {α β : Type} (x : α) (f g : α → β)
    (pointwise : ∀ y, f y = g y) : f = g := by
  fail_if_success vampire []
  vampire [pointwise]

-- Export performs the same pointwise lowering and restores the original goal.
set_option vampire.outputPath "artifacts/function-equality-export.p" in
example {α β : Type} (f g : α → β)
    (pointwise : ∀ x, f x = g x) : f = g := by
  vampire_export [pointwise]
  exact funext pointwise

set_option vampire.mockScript "Tests/scripts/does-not-exist.sh" in
example {α β : Type} (f g : α → β)
    (pointwise : ∀ x, f x = g x) : f = g := by
  fail_if_success vampire_export [pointwise]
  exact funext pointwise

#print axioms function_equality_simple
#print axioms function_equality_curried
#print axioms function_equality_dependent
#print axioms function_equality_set
#print axioms function_equality_transitive
#print axioms function_equality_application_rollback

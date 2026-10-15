import VampireHammer
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.attributeLemmas false
set_option vampire.outputPath "artifacts/first-order-encoding-ordinary.p" in
theorem ordinary (P Q : Prop) (h : P) (step : P → Q) : Q := by vampire
#print axioms ordinary

set_option vampire.outputPath "artifacts/first-order-encoding-function_objects.p" in
theorem function_objects {α β : Type} (f g : α → β)
    (accepts : (α → β) → Prop) (positive : accepts f) (rewrite : f = g) : accepts g := by
  vampire
#print axioms function_objects

set_option vampire.outputPath "artifacts/first-order-encoding-lambda_objects.p" in
theorem lambda_objects (accepts : (Nat → Nat) → Prop)
    (rule : ∀ f, (∀ x, f x = x) → accepts f) : accepts (fun x => x) := by
  vampire
#print axioms lambda_objects

set_option vampire.outputPath "artifacts/first-order-encoding-proposition_objects.p" in
theorem proposition_objects (R : Prop) (rule : ∀ P : Prop, P → R) : R := by
  vampire
#print axioms proposition_objects

-- Integer comparisons used as data need the same truth wrapper as other
-- proposition objects, including beneath a universal binder.
set_option vampire.outputPath "artifacts/first-order-encoding-integer-propositions.p" in
theorem integer_proposition_objects (x y : Int) (accepts : Prop → Prop)
    (positive : accepts (x ≤ y)) (equivalent : (x ≤ y) ↔ (x < y)) : accepts (x < y) := by
  vampire [positive, equivalent]
#print axioms integer_proposition_objects

set_option vampire.outputPath "artifacts/first-order-encoding-bound-integer-propositions.p" in
theorem bound_integer_proposition_objects (accepts : Prop → Prop)
    (rule : ∀ x y : Int, accepts (x < y)) : accepts ((0 : Int) < 1) := by
  vampire [rule]
#print axioms bound_integer_proposition_objects

-- A quantified Inhabited binder is not a domain witness. Recover a real
-- dictionary from the caller's Nonempty assumption instead.
set_option vampire.outputPath "artifacts/first-order-encoding-inhabited-domain.p" in
theorem inhabited_dictionary_domain {α : Sort u} [Nonempty α] {P : Prop}
    (rule : Inhabited α → P) : P := by
  vampire [*, Nonempty.elim]
#print axioms inhabited_dictionary_domain

private class EmptyDictionary where
  witness : Empty

example (P : EmptyDictionary → Prop) (rule : ∀ [d : EmptyDictionary], P d) : True := by
  fail_if_success have : ∃ d, P d := by vampire [rule]
  trivial

set_option vampire.outputPath "artifacts/first-order-encoding-proposition_extensionality.p" in
theorem proposition_extensionality (P Q : Prop) (equivalent : P ↔ Q) : P = Q := by
  vampire
#print axioms proposition_extensionality

-- Explicit premise selection and failed retries preserve the original goal.
set_option vampire.outputPath "artifacts/first-order-encoding-selection.p" in
example {α β : Type} (f g : α → β) (accepts : (α → β) → Prop)
    (positive : accepts f) (rewrite : f = g) : accepts g := by
  fail_if_success vampire []
  vampire [positive, rewrite]

-- Empty scalar domains cannot be populated by the function-object encoding.
set_option vampire.outputPath "artifacts/first-order-encoding-empty.p" in
example (f : Empty → Empty) : True := by
  fail_if_success have : Nonempty Empty := by vampire []
  trivial

-- Users can turn off the translation fallback.
set_option vampire.higherOrderEncoding false in
example {α β : Type} (f g : α → β) (accepts : (α → β) → Prop)
    (positive : accepts f) (rewrite : f = g) : accepts g := by
  fail_if_success vampire [positive, rewrite]
  exact rewrite ▸ positive

set_option vampire.outputPath "artifacts/first-order-encoding-function-extensionality.p" in
theorem encoded_function_extensionality (f g : Nat → Nat) (accepts : (Nat → Nat) → Prop)
    (positive : accepts f) (pointwise : ∀ x, f x = g x) : accepts g := by
  vampire [positive, pointwise]
#print axioms encoded_function_extensionality

set_option vampire.outputPath "artifacts/first-order-encoding-curried-extensionality.p" in
theorem encoded_curried_extensionality (f g : Nat → Nat → Nat)
    (accepts : (Nat → Nat → Nat) → Prop) (positive : accepts f)
    (pointwise : ∀ x y, f x y = g x y) : accepts g := by
  vampire [positive, pointwise]
#print axioms encoded_curried_extensionality

-- This lambda captures a bound variable inside a source quantifier.
set_option vampire.outputPath "artifacts/first-order-encoding-captured-lambda.p" in
theorem encoded_captured_lambda (accepts : (Nat → Nat) → Prop)
    (rule : ∀ a : Nat, accepts (fun _ => a)) : accepts (fun _ => 0) := by
  vampire [rule]
#print axioms encoded_captured_lambda

-- Defining a ground function does not imply that its argument type is inhabited.
-- Unsupported optional beta definitions can be omitted without dropping this source fact.
set_option vampire.outputPath "artifacts/first-order-encoding-empty-lambda.p" in
theorem encoded_empty_lambda (accepts : (Empty → Nat) → Prop)
    (rule : ∀ f, accepts f) : accepts (fun _ => 0) := by
  vampire [rule]
#print axioms encoded_empty_lambda

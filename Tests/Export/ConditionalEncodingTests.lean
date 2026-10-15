import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.attributeLemmas false

set_option vampire.outputPath "artifacts/conditional-positive.p" in
theorem conditional_positive {α : Type} (P : Prop) [Decidable P] (a b : α)
    (accepts : α → Prop) (positive : P) (value : accepts a) :
    accepts (if P then a else b) := by
  vampire [positive, value]
#print axioms conditional_positive

set_option vampire.outputPath "artifacts/conditional-negative.p" in
theorem conditional_negative {α : Type} (P : Prop) [Decidable P] (a b : α)
    (accepts : α → Prop) (negative : ¬ P) (value : accepts b) :
    accepts (if P then a else b) := by
  vampire [negative, value]
#print axioms conditional_negative

set_option vampire.outputPath "artifacts/conditional-compound.p" in
theorem conditional_compound {α : Type} (P Q : Prop) [Decidable P] [Decidable Q]
    (a b c : α) (accepts : α → Prop) (positive : P) (negative : ¬ Q)
    (value : accepts b) : accepts (if P then (if Q then a else b) else c) := by
  vampire [positive, negative, value]
#print axioms conditional_compound

set_option vampire.outputPath "artifacts/conditional-function.p" in
theorem conditional_function {α β : Type} (P : Prop) [Decidable P] (f g : α → β)
    (accepts : (α → β) → Prop) (positive : P) (value : accepts f) :
    accepts (if P then f else g) := by
  vampire [positive, value]
#print axioms conditional_function

set_option vampire.outputPath "artifacts/conditional-proposition.p" in
theorem conditional_proposition (P Q R : Prop) [Decidable P] (negative : ¬ P)
    (value : R) : if P then Q else R := by
  vampire [negative, value]
#print axioms conditional_proposition

-- The predicate selecting a branch depends on the surrounding binder.
set_option vampire.outputPath "artifacts/conditional-bound-test.p" in
theorem conditional_bound_test (P : Nat → Prop) [DecidablePred P]
    (accepts : Nat → Prop) (rule : ∀ n, accepts (if P n then n else 0))
    (positive : P 5) : accepts 5 := by
  vampire [rule, positive]
#print axioms conditional_bound_test

-- A partially applied conditional becomes a function object with checked
-- beta equations. Those equations must connect to the same branch operator.
set_option vampire.outputPath "artifacts/conditional-partial.p" in
theorem conditional_partial (P : Prop) [Decidable P] (positive : P)
    (accepts : (Nat → Nat → Nat) → Prop)
    (rule : ∀ f, (∀ x y, f x y = x) → accepts f) :
    accepts (fun x y => if P then x else y) := by
  vampire [positive, rule]
#print axioms conditional_partial

-- Explicit hints must still control which branch can be selected.
set_option vampire.outputPath "artifacts/conditional-selection.p" in
example (P : Prop) [Decidable P] (positive : P) : (if P then 0 else 1) = 0 := by
  fail_if_success vampire []
  vampire [positive]

-- Having a function-valued branch does not populate its possibly empty domain.
set_option vampire.outputPath "artifacts/conditional-empty.p" in
example (P : Prop) [Decidable P] (f g : Empty → Empty) (positive : P)
    (choice : (if P then f else g) = f) : True := by
  fail_if_success have : Nonempty Empty := by vampire [positive, choice]
  trivial

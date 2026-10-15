import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.attributeLemmas false

-- Preserve logical uses of a quantified proposition even when the quantified
-- domain may be empty. There are no additional Nonempty hypotheses.
set_option vampire.outputPath "artifacts/opaque-universal-or.p" in
theorem opaque_universal_or {α : Type} (P : α → Prop) (Q : Prop) (h : ∀ x, P x) :
    (∀ x, P x) ∨ Q := by
  vampire [h]
#print axioms opaque_universal_or

set_option vampire.outputPath "artifacts/opaque-functions-or.p" in
theorem opaque_functions_or {α β : Type} (P : (α → β) → Prop) (Q : Prop)
    (h : ∀ f, P f) : (∀ f, P f) ∨ Q := by
  vampire [h]
#print axioms opaque_functions_or

-- An actual existential proof supplies a function-object witness. Its domain
-- and range may still be empty; the witness does not populate either type.
set_option vampire.outputPath "artifacts/opaque-function-existence.p" in
theorem opaque_function_existence {α β : Type} (P Q : (α → β) → Prop)
    (existing : ∃ f, P f) (step : ∀ f, P f → Q f) : ∃ f, Q f := by
  vampire [existing, step]
#print axioms opaque_function_existence

set_option vampire.outputPath "artifacts/opaque-conjoined-existence.p" in
theorem opaque_conjoined_existence {α β : Type} (P Q : (α → β) → Prop) (R : Prop)
    (existing : (∃ f, P f) ∧ R) (step : ∀ f, P f → Q f) : ∃ f, Q f := by
  vampire [existing, step]
#print axioms opaque_conjoined_existence

set_option vampire.outputPath "artifacts/opaque-existence-contradiction.p" in
theorem opaque_existence_contradiction {α β : Type} (P : (α → β) → Prop)
    (existing : ∃ f, P f) (negative : ∀ f, ¬P f) : False := by
  vampire [existing, negative]
#print axioms opaque_existence_contradiction

-- A satisfiable pair of universal facts on empty domains must not acquire an
-- element from an unrelated function or from the new opaque truth symbols.
set_option vampire.outputPath "artifacts/opaque-empty-cycle.p" in
example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (positive : ∀ x, P (g (f x))) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : Nonempty α := by vampire [positive, negative]
  trivial

-- Explicit premise selection remains effective after the translation retry.
set_option vampire.outputPath "artifacts/opaque-explicit-selection.p" in
example {α : Type} (P : α → Prop) (Q : Prop) (h : ∀ x, P x) : (∀ x, P x) ∨ Q := by
  fail_if_success vampire []
  vampire [h]

-- Export remains observational when quantified propositions become opaque.
set_option vampire.outputPath "artifacts/opaque-export.p" in
example {α : Type} (P : α → Prop) (Q : Prop) (h : ∀ x, P x) : (∀ x, P x) ∨ Q := by
  vampire_export [h]
  exact Or.inl h

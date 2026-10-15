import VampireHammer

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5
set_option linter.unusedVariables false

private opaque dependentPredicate : ((n : Nat) → Fin (n + 1)) → Prop

-- Build a required local premise list directly, so automatic collection cannot
-- remove the offending hypothesis before the monomorphization regression.
open Lean Meta Elab Tactic in
elab "vampire_required_subset" "[" hints:term,* "]" : tactic => withMainContext do
  let lemmas ← hints.getElems.mapM fun hint =>
    Auto.Prep.elabLemma hint (.leaf "lctxLem recovery")
  let inhs ← Auto.Inhabitation.getInhFactsFromLCtx
  let proof ← withOptions (fun opts => opts.setBool `vampire.omitUnsupportedLocalHypotheses true) <|
    VampireHammer.Export.Internal.replayVampireWithAuto lemmas inhs
  (← getMainGoal).assign proof

-- A local existential justifies a real witness even when it was not selected
-- as a formula and its bound variable is absent from the exported signature.
theorem existential_domain_recovery {α : Type} (P : α → Prop)
    (exists_value : ∃ _ : α, True) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

-- The witness may carry useful data; extracting it does not add an assumption.
theorem existential_predicate_recovery {α : Type} (P : α → Prop)
    (positive : ∃ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

-- Neither the local element nor these functions occurs in a selected formula.
-- Their applications still justify the domain needed by those formulas.
theorem unselected_function_domain_recovery {α β γ : Type} (a : α)
    (f : α → β) (g : β → γ) (P : γ → Prop)
    (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

-- An indexed result constrains the argument to the existing index. It must
-- not unify away that index or turn a potentially empty Fin n into Fin 1.
theorem indexed_function_domain_recovery (n : Nat) (f : (k : Nat) → Fin (k + 1))
    (P : Fin (n + 1) → Prop) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

structure LocalDomainData (α β : Type) where
  point : α
  transport : α → β

-- A local record provides both a starting value and a function. No extra
-- proposition is selected and no Nonempty instance is supplied.
theorem record_domain_recovery {α β : Type} (data : LocalDomainData α β)
    (P : β → Prop) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

-- An unused dependent hypothesis must not prevent a checked refutation from
-- independent, representable premises. Its unsupported instances are omitted.
theorem unsupported_hypothesis_recovery {α : Type} (a : α) (P : α → Prop)
    (h1 : ∀ x, x ≠ a ∨ P x) (h2 : ¬P a)
    (unused : dependentPredicate (fun n => ⟨0, Nat.zero_lt_succ n⟩)) : False := by
  vampire_required_subset [h1, h2, unused]

-- Repeat through the ordinary FO route; the subset retry is encoding-neutral.
set_option vampire.higherOrder false in
example {α : Type} (a : α) (P : α → Prop)
    (h1 : ∀ x, x ≠ a ∨ P x) (h2 : ¬P a)
    (unused : dependentPredicate (fun n => ⟨0, Nat.zero_lt_succ n⟩)) : False := by
  vampire_required_subset [h1, h2, unused]

-- Without any justified witness, contradictory-looking universal statements
-- can both hold on an empty domain. Neither recovery path may invent one.
example (P : Empty → Prop) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [positive, negative]
  trivial

example (P : Fin 0 → Prop) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [positive, negative]
  trivial

-- A function into nonzero finite types does not inhabit Fin n for arbitrary n.
-- Matching an indexed result must preserve the caller's index.
example (n : Nat) (f : (k : Nat) → Fin (k + 1)) (P : Fin n → Prop)
    (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [positive, negative]
  trivial

example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [positive, negative]
  trivial

example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (positive : ∀ x, P (g (f x))) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [positive, negative]
  trivial

#print axioms existential_domain_recovery
#print axioms existential_predicate_recovery
#print axioms unselected_function_domain_recovery
#print axioms indexed_function_domain_recovery
#print axioms record_domain_recovery
#print axioms unsupported_hypothesis_recovery

import VampireHammer

open Lean Meta Elab Tactic

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- Check the converted proof as well as the proposition; a syntactic replacement
-- of HEq would leave an ill-typed proof and fail this test.
elab "check_heq_normalization " source:term " against " expected:term : tactic =>
  withMainContext do
    let proof ← Term.elabTerm source none
    let expected ← Term.elabTerm expected (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let expected ← instantiateMVars expected
    let lemma : Auto.Lemma := ⟨⟨proof, ← inferType proof, .leaf "HEq normalization test"⟩, #[]⟩
    let normalized ← VampireHammer.HeterogeneousEquality.normalizeLemma lemma
    unless ← isDefEq normalized.type expected do
      throwError "unexpected normalized proposition: {normalized.type}"
    unless (← isTypeCorrect normalized.proof) &&
        (← isDefEq (← inferType normalized.proof) normalized.type) do
      throwError "ill-typed heterogeneous equality conversion"
    unless (collectFVars {} normalized.proof).fvarIds.all (← getLCtx).contains do
      throwError "temporary binder escaped heterogeneous equality normalization"

abbrev EqualityAlias (α : Sort u) := α

example {α : Type} (a : α) (b : EqualityAlias α) (h : HEq a b) : True := by
  check_heq_normalization h against (a = b)
  trivial

example {α : Type} (f g : α → α) (h : ∀ x, ¬HEq (f x) (g x)) : True := by
  check_heq_normalization h against (∀ x, ¬(f x = g x))
  trivial

example {α : Type} {β : α → Type} (f g : (x : α) → β x)
    (h : ∀ x, HEq (f x) (g x)) : True := by
  check_heq_normalization h against (∀ x, f x = g x)
  trivial

-- Rewriting a proof-dependent binder must transport its uses too.
example {α : Type} (a b : α) (Q : HEq a b → Prop)
    (h : ∀ p, Q p) : True := by
  check_heq_normalization h against (∀ p : a = b, Q (heq_of_eq p))
  trivial

-- Unknown, genuinely distinct types must retain HEq.
example {α β : Type} (a : α) (b : β) (h : HEq a b) : True := by
  check_heq_normalization h against (HEq a b)
  trivial

set_option vampire.outputPath "artifacts/heq-to-equality.p" in
theorem heq_to_equality {α : Type} (a b : α) (h : HEq a b) : a = b := by
  vampire [h]

set_option vampire.outputPath "artifacts/equality-to-heq.p" in
theorem equality_to_heq {α : Type} (a b : α) (h : a = b) : HEq a b := by
  vampire [h]

-- Conversions in both assumptions and the negated goal must compose with
-- first-order equality reasoning, and replay must prove the original HEq goal.
set_option vampire.outputPath "artifacts/heq-transitivity.p" in
theorem heq_transitivity {α : Type} (f g t : α → α) (a : α)
    (h : HEq (f a) (g a)) (k : g a = t a) : HEq (f a) (t a) := by
  vampire [h, k]

#print axioms heq_to_equality
#print axioms equality_to_heq
#print axioms heq_transitivity

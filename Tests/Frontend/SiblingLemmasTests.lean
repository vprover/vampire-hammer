import VampireHammer
import Mathlib.Data.Int.Basic

/-!
Tests for sibling lemma discovery: unattributed environment theorems whose
statements mention propositions of the source problem. The attribute indexes
must not be consulted for these facts, so every candidate here is either a
plain local theorem or an Int-specific mathlib lemma that no simp/grind
pattern specializes to the Integer type.
-/

open Lean Meta Elab Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option vampire.siblingLemmas true

namespace SiblingLemmasTests

-- No simp or grind attribute: invisible to the attribute collector.
private def sibPred (n : Nat) : Prop := n % 2 = 0
private theorem sib_pred_iff (n : Nat) : sibPred n ↔ n % 2 = 0 := .rfl

private def sibTwice (n : Nat) : Nat := n + n
private theorem sib_twice_eq (n : Nat) : sibTwice n = 2 * n := by simp [sibTwice]; omega

elab "check_selected " source:term " using " declaration:ident : tactic => withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let expected ← realizeGlobalConstNoOverloadWithInfo declaration
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.SiblingLemmas.collect #[fact]
    unless selected.all (fun fact => !fact.proof.hasMVar && !fact.type.hasMVar) do
      throwError "selected fact contains unresolved metavariables"
    unless selected.any (fun fact => (fact.proof.find? (·.isConstOf expected)).isSome) do
      throwError "did not select {expected} for {expression}"

elab "check_absent " source:term " without " declaration:ident : tactic => withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let rejected ← realizeGlobalConstNoOverloadWithInfo declaration
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.SiblingLemmas.collect #[fact]
    if selected.any (fun fact => (fact.proof.find? (·.isConstOf rejected)).isSome) then
      throwError "selected {rejected} for {expression} although its theory does not match"

elab "check_excluded " source:term " excluding " declaration:ident : tactic => withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let excluded ← realizeGlobalConstNoOverloadWithInfo declaration
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.SiblingLemmas.collect #[fact] (some excluded)
    if selected.any (fun fact => (fact.proof.find? (·.isConstOf excluded)).isSome) then
      throwError "selected the excluded theorem itself"

/-- A sibling proved from the theorem being reproved only restates the goal; the
audit of a reproof rejects every proof using it, so such clones must not even
enter the premise pool. The target statement is a proper part of the source
fact, so the clone's specialization is not deduplicated as an exact copy. -/
elab "check_no_clone " source:term " proving " target:ident " without " clone:ident : tactic =>
    withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let proved ← realizeGlobalConstNoOverloadWithInfo target
  let cloneName ← realizeGlobalConstNoOverloadWithInfo clone
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.SiblingLemmas.collect #[fact] (some proved)
    if selected.any (fun fact => (fact.proof.find? (·.isConstOf cloneName)).isSome) then
      throwError "selected {cloneName}, which is proved from the target {proved}"
    if selected.isEmpty then
      throwError "no sibling selected at all for {expression}"

example : True := by
  check_selected (sibPred 4) using sib_pred_iff
  trivial

-- Query terms are collected beneath binders with metavariables, as in attribute anchoring.
example : True := by
  check_selected (∀ n : Nat, sibPred n) using sib_pred_iff
  trivial

-- A sibling whose specialization coincides with the source fact adds nothing and
-- is deduplicated; it is selected from a fact of which it is a proper part.
example (k : Nat) : True := by
  check_selected (sibTwice k = 2 * k ∨ sibTwice k = 1) using sib_twice_eq
  trivial

-- The Int-specific sibling is retrieved for an Int equality even though its
-- statement carries no attribute; the Nat analogue fails the definitional check.
example (a b : Int) : True := by
  check_selected (a * b = 0) using Int.mul_eq_zero
  check_absent (a * b = 0) without Nat.mul_eq_zero
  trivial

example (a b : Int) : True := by
  check_excluded (a * b = 0) excluding Int.mul_eq_zero
  trivial

-- The theorem being reproved and an environment clone proved from it.
private theorem cloneTarget (n : Nat) : 2 * n = n + n := by omega
private theorem cloneAlias (n : Nat) : 2 * n = n + n := cloneTarget n

-- A sibling proved from the theorem being reproved only restates the goal; the
-- audit of a reproof rejects every proof using it, so it must not even enter
-- the premise pool. Independent siblings of the same anchor remain eligible.
example (k : Nat) : True := by
  check_no_clone (2 * k = k + k ∨ k = 0) proving cloneTarget without cloneAlias
  trivial

-- Discovery is disabled unless the option is set.
set_option vampire.siblingLemmas false in
example : True := by
  fail_if_success check_selected (sibPred 4) using sib_pred_iff
  trivial

-- End to end: the Int-specific sibling is discovered as a premise and closes a
-- goal that the simp-indexed generic `MulZeroClass.mul_eq_zero` cannot unify.
set_option vampire.outputPath "artifacts/sibling-lemmas/int.p" in
theorem int_mul_eq_zero_or (a b : Int) (h : a * b = 0) : a = 0 ∨ b = 0 := by
  vampire [h]
#print axioms int_mul_eq_zero_or

end SiblingLemmasTests

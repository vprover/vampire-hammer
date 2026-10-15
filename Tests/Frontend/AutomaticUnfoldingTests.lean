import VampireHammer
import Mathlib.Logic.Function.Basic

open Lean Meta Elab Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option vampire.attributeLemmas false

namespace AutomaticUnfoldingTests

private def relationalTransitive {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z
private def both (p q : Prop) : Prop := p ∧ q
private def wrapped {α : Type} (P : α → Prop) (x : α) : Prop := P x
private def nested {α : Type} (P : α → Prop) (x : α) : Prop := wrapped P x
private def scalarPredicate (n : Nat) : Prop := n = 0
private def instanceOnly {α : Type} [DecidableEq α] (x : α) : α := x
private def explicitDecision {α : Type} (_decision : DecidableEq α) (x : α) : α := x
private def instanceAndPredicate {α : Type} [DecidableEq α]
    (P : α → Prop) (x : α) : Prop := P x

elab "check_unfold " source:term " becomes " expected:term : tactic => withMainContext do
  let expression ← Term.elabTerm source none
  let expected ← Term.elabTerm expected none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let expected ← instantiateMVars expected
  let unfolded ← VampireHammer.SourceNormalization.unfoldForFirstOrder expression
  unless unfolded == expected do
    throwError "unexpected unfolding: {unfolded}; expected {expected}"

example {α : Type} (P : α → Prop) (x : α) (p q : Prop) : True := by
  check_unfold (nested P x) becomes (P x)
  check_unfold (both p q) becomes (p ∧ q)
  -- Already first-order symbols stay opaque, even when definitions exist.
  check_unfold (scalarPredicate 0) becomes (scalarPredicate 0)
  trivial

-- A function-shaped instance is a monomorphization parameter. An ordinary
-- function argument still requires unfolding when an instance precedes it.
example {α : Type} [DecidableEq α] (P : α → Prop) (x : α) : True := by
  check_unfold (instanceOnly x) becomes (instanceOnly x)
  check_unfold (explicitDecision (inferInstance : DecidableEq α) x) becomes (x)
  check_unfold (instanceAndPredicate P x) becomes (P x)
  trivial

set_option vampire.autoUnfoldLimit 0 in
example {α : Type} (P : α → Prop) (x : α) : True := by
  check_unfold (nested P x) becomes (nested P x)
  trivial

set_option vampire.autoUnfoldLimit 1 in
example {α : Type} (P : α → Prop) (x : α) : True := by
  check_unfold (nested P x) becomes (wrapped P x)
  trivial

set_option vampire.autoUnfold false in
example {α : Type} (P : α → Prop) (x : α) : True := by
  check_unfold (nested P x) becomes (nested P x)
  trivial

set_option vampire.outputPath "artifacts/automatic-unfolding/custom-relation.p" in
theorem custom_relation {α : Type} (R : α → α → Prop) (a b c : α)
    (ht : relationalTransitive R) (hab : R a b) (hbc : R b c) : R a c := by
  vampire [ht, hab, hbc]

set_option vampire.outputPath "artifacts/automatic-unfolding/prop-wrapper.p" in
theorem prop_wrapper (p q : Prop) (h : both p q) : p := by
  vampire [h]

#print axioms custom_relation
#print axioms prop_wrapper

end AutomaticUnfoldingTests

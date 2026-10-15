import VampireHammer
import Mathlib.Data.Int.Order.Basic

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- Its law has a dependent data binder that Auto cannot monomorphize.
private opaque acceptsDependent : ((n : Nat) → Fin (n + 1)) → Prop := fun _ => True

class OptionalDependentLaw : Type where
  law : acceptsDependent (fun n => ⟨0, Nat.zero_lt_succ n⟩)

-- Unrelated automatic laws must not prevent an ordinary first-order proof.
set_option vampire.outputPath "artifacts/optional-dependent-law.p" in
theorem optional_dependent_law_replay [OptionalDependentLaw] (P : Prop)
    (positive : P) (negative : ¬P) : False := by
  vampire [positive, negative]

#print axioms optional_dependent_law_replay

-- An unsupported explicit hint instance can be omitted on the existing
-- monomorphization retry. Independent supported hints must still prove the goal.
theorem unsupported_explicit_hint_replay [OptionalDependentLaw] (P : Prop)
    (positive : P) (negative : ¬P) : False := by
  vampire [positive, negative, OptionalDependentLaw.law]

#print axioms unsupported_explicit_hint_replay

-- Unsupported required formulas must produce an export error. In particular,
-- silently dropping the negated goal over an unsupported domain would send an
-- empty SAT query.
open Lean Elab Tactic in
elab "expect_export_error " invocation:tactic : tactic => do
  let saved ← saveState
  let message ← try
    evalTactic invocation
    pure "unexpected success"
  catch error => error.toMessageData.toString
  saved.restore
  unless message.contains "TFF export:" && message.contains "unsupported domain" do
    throwError "expected an unsupported domain export diagnostic, got: {message}"

-- Function objects remain unsupported when their checked encoding is disabled.
-- Check required goals and explicit hints separately, without a direct proof
-- bypassing the export path or parallel native HO search proving the goal.
private opaque acceptsFunction : (Nat → Nat) → Prop

set_option vampire.parallel false in
set_option vampire.routedSlices false in
set_option vampire.higherOrderEncoding false in
set_option vampire.directProof false in
example (f : Nat → Nat) (h : acceptsFunction f) : acceptsFunction f := by
  expect_export_error vampire [h]
  exact h

set_option vampire.higherOrderEncoding false in
example (f : Nat → Nat) (h : acceptsFunction f) (P : Prop) (p : P) : P := by
  expect_export_error vampire_export [h, p]
  exact p


class UsableAutomaticLaw (P Q : Nat → Prop) : Prop where
  transfer : ∀ n, P n → Q n

-- An unsupported automatic fact must not discard an independent usable law.
set_option vampire.outputPath "artifacts/optional-law-preservation.p" in
theorem usable_automatic_law_survives (P Q : Nat → Prop)
    [OptionalDependentLaw] [UsableAutomaticLaw P Q] (n : Nat) (p : P n) : Q n := by
  vampire [p]

-- Reverse the instance order to check failed abstraction leaves no stale binders.
set_option vampire.outputPath "artifacts/optional-law-preservation-reversed.p" in
theorem usable_automatic_law_survives_reversed (P Q : Nat → Prop)
    [UsableAutomaticLaw P Q] [OptionalDependentLaw] (n : Nat) (p : P n) : Q n := by
  vampire [p]

#print axioms usable_automatic_law_survives
#print axioms usable_automatic_law_survives_reversed

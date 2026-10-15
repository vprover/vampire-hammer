import VampireHammer

open Lean Meta Elab Tactic

-- These must close before any external process is invoked.
set_option vampire.executable "/missing-vampire-substitution-regression"

theorem selected_dependent_substitution {α : Type u} {β : α → Type v}
    (x y : α) (h : x = y) (f : (a : α) → β a) : HEq (f x) (f y) := by
  vampire [h]

theorem selected_substitution_chain {α : Type u} {β : α → Type v}
    (x y z : α) (h : x = y) (k : y = z) (f : (a : α) → β a) : HEq (f x) (f z) := by
  vampire [h, k]

theorem selected_substitution_reverse {α : Type u} {β : α → Type v}
    (x y : α) (h : y = x) (f : (a : α) → β a) : HEq (f x) (f y) := by
  vampire [h]

-- Equality elimination must respect explicit premise selection.
example {α : Type u} {β : α → Type v} (x y : α) (h : x = y)
    (f : (a : α) → β a) : HEq (f x) (f y) := by
  fail_if_success vampire []
  exact selected_dependent_substitution x y h f

-- A failed substitution attempt must restore the caller's context for replay.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
theorem failed_substitution_preserves_replay {α : Type} (x y : α) (h : x = y)
    (P Q : Prop) (p : P) : Q ∨ P := by
  vampire [h, p]

#print axioms selected_dependent_substitution
#print axioms selected_substitution_chain
#print axioms selected_substitution_reverse
#print axioms failed_substitution_preserves_replay

-- Exhausting the optional direct route must still allow checked replay with
-- the original goal and selected premises.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.directProofHeartbeats 0 in
theorem disabled_direct_budget_preserves_replay (P Q : Prop)
    (positive : P) (step : P → Q) : Q := by
  vampire [positive, step]
#print axioms disabled_direct_budget_preserves_replay

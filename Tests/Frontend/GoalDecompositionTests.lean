import VampireHammer

set_option vampire.attributeLemmas false
set_option vampire.timeLimit 2

namespace GoalDecompositionTests

structure Laws (P Q : Prop) : Prop where
  first : P
  second : Q

-- Splitting logical records introduces no data witnesses.
set_option vampire.outputPath "artifacts/goal-decomposition/record.p" in
theorem record (P Q : Prop) (p : P) (q : Q) : Laws P Q := by
  vampire [p, q]

set_option vampire.outputPath "artifacts/goal-decomposition/nested.p" in
theorem nested (P Q R : Prop) (p : P) (q : Q) (r : R) : P ∧ (Q ∧ R) := by
  vampire [p, q, r]

-- Existing hypotheses excluded by explicit hints must remain excluded even
-- from target simplification. Failure rolls the original goal back intact.
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  fail_if_success vampire [p]
  exact ⟨p, q⟩

example : (∃ n : Nat, n = n) := by
  -- Test structural preparation directly: the upgraded replay pipeline can
  -- prove this existential without choosing a witness during decomposition.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    unless (← VampireHammer.GoalDecomposition.split? goal 8).isNone do
      throwError "Structural preparation selected an existential witness"
  exact ⟨0, rfl⟩

example : (∃ n : Nat, n = n) := by
  vampire []

-- Do not discard another user goal while switching between branch goals.
example (P Q R : Prop) (p : P) (q : Q) (r : R) : (P ∧ Q) ∧ R := by
  constructor
  · vampire [p, q]
  · exact r

-- At least one leaf must run through export and replay rather than direct
-- constructor assignment or reflexivity.
set_option vampire.outputPath "artifacts/goal-decomposition/replay.p" in
theorem replay (α : Type) (R : α → α → Prop) (a b c : α)
    (trans : ∀ x y z, R x y → R y z → R x z) (ab : R a b) (bc : R b c) :
    R a c ∧ R a b := by
  vampire [trans, ab, bc]

structure Pair where
  first : Nat
  second : Nat

@[ext] theorem pair_ext (x y : Pair) (first : x.first = y.first)
    (second : x.second = y.second) : x = y := by
  cases x
  cases y
  cases first
  cases second
  rfl

set_option vampire.outputPath "artifacts/goal-decomposition/ext.p" in
theorem ext (x y : Pair) (first : x.first = y.first) (second : x.second = y.second) : x = y := by
  vampire [first, second]

#print axioms record
#print axioms nested
#print axioms replay

end GoalDecompositionTests

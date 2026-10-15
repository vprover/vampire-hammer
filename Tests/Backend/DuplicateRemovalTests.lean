import VampireHammer.Backend.Factoring

open Lean Meta Elab Tactic
open VampireHammer.Clause
open VampireHammer.Backend.Internal

elab "contract_duplicates " parent:term : tactic => withMainContext do
  let parent ← Term.elabTerm parent none
  let target ← getMainTarget
  let some (_, source) ← clauseView parent (← inferType parent)
    | throwError "expected a source clause"
  let placeholder ← mkFreshExprMVar target
  let some (_, targetLiterals) ← clauseView placeholder target
    | throwError "expected a target clause"
  let some (_, proof) ← VampireHammer.Backend.removeDuplicateClause parent source targetLiterals
    | throwError "not a duplicate contraction"
  unless ← isTypeCorrect proof do throwError "ill-typed contraction proof"
  unless ← isDefEq (← inferType proof) target do throwError "wrong contraction result"
  (← getMainGoal).assign proof
  replaceMainGoal []

-- Multiple groups; preserving a later occurrence must also be supported.
example (A B C : Prop) (h : Holds [A, B, A, C, B, C]) : Holds [B, A, C] := by
  contract_duplicates h

-- This shape used to explore many failed deletion orders before keeping
-- the initial occurrences. The generated proof is checked by the kernel.
set_option maxHeartbeats 200000 in
example (A B C D E F G H : Prop)
    (h : Holds [A, B, C, D, E, F, G, H, H, G, F, E, D, C, B, A]) :
    Holds [A, B, C, D, E, F, G, H] := by
  contract_duplicates h

example {α : Type} (a b : α) (P : Prop)
    (h : Holds [a = b, P, b = a, a ≠ b, b ≠ a]) : Holds [b = a, P, b ≠ a] := by
  contract_duplicates h

-- Definitional aliases and retained multiplicities.
example (A B : Prop) (h : Holds [A, A, B, A]) : Holds [id A, A, B] := by
  contract_duplicates h

example (h : Holds []) : Holds [] := by
  contract_duplicates h

-- A changed occurrence order is certified by the explicit permutation bridge.
example (A B : Prop) (h : Holds [A, A, B]) : Holds [B, A] := by
  contract_duplicates h

-- Reject deleting a unique literal, polarity changes, and
-- introducing occurrences. A separately supplied target proves the goal
-- after the rejection check; it is never passed to the contraction helper.
example (A B : Prop) (h : Holds [A, B, A]) (target : Holds [A]) : Holds [A] := by
  fail_if_success contract_duplicates h
  exact target

example {α : Type} (a b : α) (h : Holds [a = b, b = a])
    (target : Holds [a ≠ b]) : Holds [a ≠ b] := by
  fail_if_success contract_duplicates h
  exact target

example (A : Prop) (h : Holds [A]) (target : Holds [A, A]) : Holds [A, A] := by
  fail_if_success contract_duplicates h
  exact target

example (A : Prop) (h : Holds [A, A]) (target : Holds []) : Holds [] := by
  fail_if_success contract_duplicates h
  exact target

import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false
set_option vampire.routedSlices false

open Lean Meta Elab Command

set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5

theorem attributed_fo {α : Type} (a : α) (P : α → Prop)
    (h1 : ∀ x, x ≠ a ∨ P x) (h2 : ¬P a) : False := by
  vampire [h1, h2]

set_option vampire.higherOrder true in
set_option vampire.higherOrderFallback false in
set_option vampire.directProof false in
theorem attributed_ho (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

-- Discarded speculative proof terms must not influence the final route.
theorem discarded_attribution (h : False) : False := by
  first
  | have := VampireHammer.Replay.firstOrderRefutation h
    fail "discard speculative reconstruction"
  | exact h

-- A reference to an earlier theorem is not reconstruction in this attempt.
theorem previously_attributed (h : False) : False := VampireHammer.Replay.firstOrderRefutation h
theorem direct_use_of_premise (h : False) : False := previously_attributed h

private def checkModes (name : Name) (expected : Array String) : MetaM Unit := do
  let some proof := (← getConstInfo name).value? (allowOpaque := true) | throwError "missing proof"
  let modes := VampireHammer.Replay.reconstructionModes proof
  unless modes == expected do throwError "expected {expected}, got {modes} for {name}"

run_cmd liftTermElabM do
  checkModes ``attributed_fo #["fo"]
  checkModes ``attributed_ho #["ho"]
  checkModes ``discarded_attribution #[]
  checkModes ``direct_use_of_premise #[]

#print axioms attributed_fo
#print axioms attributed_ho

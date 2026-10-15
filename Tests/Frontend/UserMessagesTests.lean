import VampireHammer

open Lean Meta Elab Tactic

-- The defaults are part of the public interface.
run_cmd do
  let options : Options := {}
  unless vampire.timeLimit.get options == 10 && vampire.routedSlices.get options &&
      !vampire.higherOrderFallback.get options && vampire.quiet.get options &&
      vampire.parallel.get options && vampire.portfolioCores.get options == 1 &&
      vampire.cache.get options do
    throwError "unexpected tactic defaults"

#guard_msgs in
example (h : True) : True := by
  vampire [h]

/-- info: vampire closed the goal. -/
#guard_msgs in
example (h : True) : True := by
  vampire [h] (quiet := false)

-- Verify actual tactic errors without depending on source positions.
elab "expect_vampire_error " expected:str " in " action:tacticSeq : tactic => do
  let saved ← saveState
  let failure ← try
    evalTactic action
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  let some message := failure | throwError "expected vampire to fail"
  unless message.contains expected.getString do
    throwError "expected `{expected.getString}` in:\n{message}"

example : True := by
  expect_vampire_error "between 0 and 100" in vampire (sliceHoFirst := 101)
  expect_vampire_error "total at most 100%" in vampire (sliceHoFirst := 50) (sliceFo := 80)
  expect_vampire_error "For unlimited search" in vampire (parallel := false) (timeout := 0)
  expect_vampire_error "expected `true` or `false`" in vampire (quiet := 1)
  expect_vampire_error "unknown setting" in vampire (notAnOption := true)
  expect_vampire_error "unknown setting" in vampire (stagedSearch := true)
  expect_vampire_error "unknown setting" in vampire (routedSearch := true)
  expect_vampire_error "unknown setting" in vampire (routeOverride := "ho")
  expect_vampire_error "unknown setting" in vampire (prepareHigherOrderAsync := false)
  trivial

-- A missing executable should give its path and a concrete setup action.
example (P : Prop) (h : P) : P := by
  expect_vampire_error "Could not start Vampire executable `/definitely/missing/vampire`" in
    vampire [h] (directProof := false) (decomposeGoals := false)
      (executable := "/definitely/missing/vampire")
  expect_vampire_error "Build the bundled prover with `lake build vampire`" in
    vampire [h] (directProof := false) (decomposeGoals := false)
      (executable := "/definitely/missing/vampire")
  exact h

-- Opting out of parallel search retains the routed schedule and shared budget.
set_option vampire.parallel false

set_option vampire.executable "Tests/testdata/scripts/mock-slice-search.py" in
set_option vampire.outputPath "artifacts/default-routed-slices.p" in
set_option vampire.directProof false in
set_option vampire.decomposeGoals false in
theorem default_routed_slices (P Q : Nat → Prop)
    (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let native ← IO.FS.readFile "artifacts/default-routed-slices.p.ho-first.stderr"
  let firstOrder ← IO.FS.readFile "artifacts/default-routed-slices.p.stderr"
  unless native.contains "stage: ho; limit: 20d" && firstOrder.contains "stage: fo" do
    throw <| IO.userError "default schedule did not run HO then FO with a 10-second budget"
  let limit := (firstOrder.splitOn "limit: ")[1]!.splitOn "d" |>.head! |>.toNat!
  unless limit > 70 && limit < 100 do
    throw <| IO.userError "FO did not receive the unused shared budget"

-- With slicing disabled, higherOrder selects the single representation.
set_option vampire.executable "Tests/testdata/scripts/mock-slice-search.py" in
set_option vampire.outputPath "artifacts/selected-fo-mode.p" in
set_option vampire.directProof false in
set_option vampire.decomposeGoals false in
theorem selected_fo_mode (P Q : Nat → Prop)
    (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp] (routedSlices := false) (higherOrder := false)

set_option vampire.executable "Tests/testdata/scripts/mock-slice-search.py" in
set_option vampire.outputPath "artifacts/selected-ho-mode.p" in
set_option vampire.directProof false in
set_option vampire.decomposeGoals false in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  -- This mock times out on HO and proves FO: an implicit FO retry would make
  -- this unexpectedly succeed and overwrite the retained native input.
  fail_if_success vampire [h, hp] (routedSlices := false) (higherOrder := true)
  exact h 0 hp

#eval show IO Unit from do
  let firstOrder ← IO.FS.readFile "artifacts/selected-fo-mode.p"
  let native ← IO.FS.readFile "artifacts/selected-ho-mode.p"
  unless firstOrder.contains "tff(" && !firstOrder.contains "thf(" &&
      native.contains "thf(" && !native.contains "tff(" do
    throw <| IO.userError "higherOrder did not select the single representation"

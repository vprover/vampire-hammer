import VampireHammer

-- Exercise the single-route protocol independently of the default sliced search.
set_option vampire.routedSlices false

open Lean Elab Command

run_cmd do
  let path := "artifacts/goal-decomposition/shared-budget.calls"
  IO.FS.createDirAll "artifacts/goal-decomposition"
  if ← System.FilePath.pathExists path then IO.FS.removeFile path

set_option vampire.executable "Tests/testdata/scripts/mock-shared-budget.sh"
set_option vampire.timeLimit 3
set_option vampire.attributeLemmas false
set_option vampire.use_portfolio false
set_option vampire.outputPath "artifacts/goal-decomposition/shared-budget.p" in
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  -- The original query fails after one second; the structural branch must
  -- receive the remainder, rather than a new three-second budget.
  fail_if_success vampire []
  exact ⟨p, q⟩

run_cmd do
  let calls ← IO.FS.readFile "artifacts/goal-decomposition/shared-budget.calls"
  unless calls.trimAscii.toString.splitOn "\n" == ["3", "1"] do
    throwError "branch/fallback searches did not share their budget: {calls}"

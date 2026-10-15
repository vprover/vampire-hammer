import VampireHammer

-- Exercise the sequential FO record-law retry and its five-second allowance.
set_option vampire.parallel false
set_option vampire.routedSlices false
set_option vampire.timeLimit 5

set_option vampire.executable "Tests/testdata/scripts/mock-record-law-retry.sh"
set_option vampire.outputPath "artifacts/record-law-retry.p"

structure RetryRecord (P : Nat → Prop) : Type where
  evidence : ∀ n, P n

private def resetRetryArtifacts : IO Unit := do
  for file in ["artifacts/record-law-retry.calls", "artifacts/record-law-retry.args"] do
    if ← (file : System.FilePath).pathExists then IO.FS.removeFile file

private def checkRetryArtifacts (unlimited : Bool) : IO Unit := do
  let calls ← IO.FS.readFile "artifacts/record-law-retry.calls"
  unless calls == "first\nsecond\n" do throw <| IO.userError "expected exactly two searches"
  let first ← IO.FS.readFile "artifacts/record-law-retry.p.with-record-laws.stdout"
  unless first.contains "SZS status Satisfiable" do throw <| IO.userError "first outcome not preserved"
  let input ← IO.FS.readFile "artifacts/record-law-retry.p.with-record-laws"
  let retried ← IO.FS.readFile "artifacts/record-law-retry.p"
  if input == retried then throw <| IO.userError "ordinary record laws were not removed"
  let arguments ← IO.FS.readFile "artifacts/record-law-retry.args"
  let budgets := (arguments.splitOn "--time_limit\n").drop 1 |>.map fun part =>
    part.splitOn "\n" |>.head! |>.toNat!
  if unlimited then
    unless budgets == [0, 0] do throw <| IO.userError "unlimited search setting changed"
  else
    unless budgets.length == 2 && budgets[0]! == 5 && budgets[1]! > 0 &&
        budgets[1]! < 5 do throw <| IO.userError "retry exceeded the shared search budget"

#eval resetRetryArtifacts

-- The mock deliberately reports SAT once. The second invocation runs the real
-- frozen prover; reconstruction checks a proof using only the selected p.
theorem record_law_retry_preserves_proof (P : Nat → Prop) (record : RetryRecord P)
    (Q R : Prop) (p : Q) : Q ∨ R := by
  vampire [p]

#eval checkRetryArtifacts false

#eval resetRetryArtifacts

set_option vampire.timeLimit 0 in
theorem record_law_retry_unlimited (P : Nat → Prop) (record : RetryRecord P)
    (Q R : Prop) (p : Q) : Q ∨ R := by
  vampire [p]

#eval checkRetryArtifacts true

#print axioms record_law_retry_preserves_proof
#print axioms record_law_retry_unlimited

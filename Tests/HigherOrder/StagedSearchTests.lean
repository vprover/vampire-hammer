import VampireHammer

set_option vampire.routedSlices false
run_cmd Lean.Elab.Command.modifyScope fun scope =>
  { scope with opts := scope.opts.set `vampire.internal.stagedSearch true }
set_option vampire.directProof false
set_option vampire.decomposeGoals false
set_option vampire.timeLimit 10
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option linter.unusedVariables false

-- The same mock is selected through names identifying the transition to test.
#eval show IO Unit from do
  IO.FS.createDirAll "artifacts"
  for mode in ["fallback", "satisfiable", "fo-success"] do
    let result ← IO.Process.output { cmd := "ln", args := #["-sf",
      "../Tests/testdata/scripts/mock-staged-search.py", s!"artifacts/mock-staged-{mode}.py"] }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr

set_option vampire.executable "artifacts/mock-staged-fallback.py" in
set_option vampire.outputPath "artifacts/staged-fallback.p" in
theorem staged_fallback (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let sat ← IO.FS.readFile "artifacts/staged-fallback.p.fo.p.fmb.stderr"
  let fo ← IO.FS.readFile "artifacts/staged-fallback.p.fo.p.stderr"
  let ho ← IO.FS.readFile "artifacts/staged-fallback.p.stderr"
  unless sat.contains "stage: sat; limit: 5d" && fo.contains "stage: fo; limit: 25d" do
    throw <| IO.userError "stages did not receive 5% and 25% of the initial budget"
  let limit := (ho.splitOn "limit: ")[1]!.splitOn "d" |>.head! |>.toNat!
  unless ho.contains "stage: ho" && limit < 100 && limit > 25 do
    throw <| IO.userError "HO did not receive the remaining budget"
  let text ← IO.FS.readFile "artifacts/staged-fallback.p"
  unless text.contains "thf(" do throw <| IO.userError "HO input was not retained"

-- A model of the FO abstraction skips FO, but must not suppress HO search.
set_option vampire.executable "artifacts/mock-staged-satisfiable.py" in
set_option vampire.outputPath "artifacts/staged-satisfiable.p" in
theorem staged_satisfiable (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  if ← System.FilePath.pathExists "artifacts/staged-satisfiable.p.fo.p.stdout" then
    throw <| IO.userError "FO search ran despite a model of the FO abstraction"
  let ho ← IO.FS.readFile "artifacts/staged-satisfiable.p.stderr"
  unless ho.contains "stage: ho" do throw <| IO.userError "SAT precheck prevented HO"

-- FO success returns a checked proof and discards speculative HO preparation.
set_option vampire.executable "artifacts/mock-staged-fo-success.py" in
set_option vampire.outputPath "artifacts/staged-fo-success.p" in
theorem staged_fo_success (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let fo ← IO.FS.readFile "artifacts/staged-fo-success.p.fo.p.stdout"
  unless fo.contains "SZS status Theorem" || fo.contains "SZS status Unsatisfiable" do
    throw <| IO.userError "FO proof missing"
  if ← System.FilePath.pathExists "artifacts/staged-fo-success.p.stdout" then
    throw <| IO.userError "HO search ran after FO succeeded"

-- The non-overlapping mode retains the same checked HO replay.
run_cmd Lean.Elab.Command.modifyScope fun scope =>
  { scope with opts := scope.opts.set `vampire.internal.prepareHigherOrderAsync false }
set_option vampire.executable "artifacts/mock-staged-fallback.py" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

-- Neither encoding may turn a potentially empty domain into a contradiction.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example {α : Type} (P : α → Prop) (h : ∀ x, P x) (hn : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [h, hn]
  trivial

#print axioms staged_fallback
#print axioms staged_satisfiable
#print axioms staged_fo_success

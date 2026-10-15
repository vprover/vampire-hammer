import VampireHammer

set_option vampire.directProof false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.decomposeGoals false
set_option vampire.higherOrderSearchRetry false
set_option vampire.timeLimit 5

open Lean Meta VampireHammer.Export.Internal

#eval show IO Unit from do
  IO.FS.createDirAll "artifacts"
  for mode in ["fo-wins", "ho-wins", "bad-replay", "both-fail", "split"] do
    for stage in ["fo", "ho"] do
      let path := s!"artifacts/mock-parallel-{mode}.{stage}.started"
      if ← System.FilePath.pathExists path then IO.FS.removeFile path
      let unsplit := s!"artifacts/mock-parallel-{mode}.unsplit.{stage}.pid"
      if ← System.FilePath.pathExists unsplit then IO.FS.removeFile unsplit
    let result ← IO.Process.output { cmd := "ln", args := #["-sf",
      "../Tests/testdata/scripts/mock-parallel-search.py", s!"artifacts/mock-parallel-{mode}.py"] }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr
  for route in ["fo", "ho"] do
    let output := s!"artifacts/parallel-split.split.branch-0.p.{route}.p.stdout"
    if ← System.FilePath.pathExists output then IO.FS.removeFile output

-- The mocks refuse to prove anything until BOTH routes are running. The
-- losing route takes 20 seconds unless cancelled; the winner is kernel checked.
set_option vampire.executable "artifacts/mock-parallel-fo-wins.py" in
set_option vampire.outputPath "artifacts/parallel-fo" in
set_option vampire.portfolioCores 2 in
theorem parallel_fo (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let pid ← IO.FS.readFile "artifacts/mock-parallel-fo-wins.ho.started"
  let alive ← IO.Process.output { cmd := "kill", args := #["-0", pid] }
  unless alive.exitCode != 0 do
    throw <| IO.userError "HO was not cancelled and joined"
  let args ← IO.FS.readFile "artifacts/parallel-fo.fo.p.stderr"
  unless args.contains "--mode portfolio --cores 2" do
    throw <| IO.userError "portfolio worker count was not forwarded"

set_option vampire.executable "artifacts/mock-parallel-ho-wins.py" in
theorem parallel_ho (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let pid ← IO.FS.readFile "artifacts/mock-parallel-ho-wins.fo.started"
  let alive ← IO.Process.output { cmd := "kill", args := #["-0", pid] }
  unless alive.exitCode != 0 do
    throw <| IO.userError "FO was not cancelled and joined"

-- A purported refutation that cannot replay must not win the race.
set_option vampire.executable "artifacts/mock-parallel-bad-replay.py" in
theorem parallel_checked (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

-- Both failures leave the caller's goal and hypotheses usable.
set_option vampire.executable "artifacts/mock-parallel-both-fail.py" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  fail_if_success vampire [h, hp]
  exact h 0 hp

set_option vampire.decomposeGoals true in
set_option vampire.executable "artifacts/mock-parallel-split.py" in
set_option vampire.outputPath "artifacts/parallel-split" in
theorem parallel_split (α : Type) (R : α → α → Prop) (a b c : α)
    (trans : ∀ x y z, R x y → R y z → R x z) (ab : R a b) (bc : R b c) :
    R a c ∧ R a b := by
  vampire [trans, ab, bc]

#eval show IO Unit from do
  unless (← System.FilePath.pathExists "artifacts/parallel-split.split.branch-0.p.fo.p.stdout") ||
      (← System.FilePath.pathExists "artifacts/parallel-split.split.branch-0.p.ho.p.stdout") do
    throw <| IO.userError "split goal never searched a branch"
  for route in ["fo", "ho"] do
    let path := s!"artifacts/mock-parallel-split.unsplit.{route}.pid"
    if ← System.FilePath.pathExists path then
      let alive ← IO.Process.output { cmd := "kill", args := #["-0", ← IO.FS.readFile path] }
      unless alive.exitCode != 0 do throw <| IO.userError "unsplit search survived"

-- Portfolio workers can also be enabled independently of the tactic race.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire (parallel := false) (routedSlices := false) (portfolioCores := 2) [h, hp]

-- Unlimited parallel search overrides the default finite sliced schedule.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire (timeout := 0) [h, hp]

-- Committing a worker's tactic state must preserve the other user goals.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 ∧ P 0 := by
  constructor
  · vampire [h, hp]
  · exact hp

-- Parallelism cannot assume that a potentially empty sort is inhabited.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example {α : Type} (P : α → Prop) (h : ∀ x, P x) (hn : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [h, hn]
  trivial

-- Test the isolation primitive without an external prover: both workers have
-- started before either can finish, and only the winning assignment survives.
#eval show Elab.TermElabM Unit from do
  let goal ← mkFreshExprMVar (mkConst ``True)
  let first ← IO.mkRef false
  let second ← IO.mkRef false
  let branch (wins : Bool) : MetaM Unit := do
    (if wins then first else second).set true
    while !(← (if wins then second else first).get) do
      Core.checkInterrupted
      IO.sleep 10
    if wins then goal.mvarId!.assign (mkConst ``True.intro)
    else
      while true do
        Core.checkInterrupted
        IO.sleep 10
  raceMeta #[branch false, branch true]
  unless (← instantiateMVars goal) == mkConst ``True.intro do
    throwError "winner's metavariable assignment was lost"

#print axioms parallel_fo
#print axioms parallel_ho
#print axioms parallel_checked
#print axioms parallel_split

import VampireHammer

-- Exercise the single-route protocol independently of the default sliced search.
set_option vampire.routedSlices false

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.directProof false
set_option vampire.decomposeGoals false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/mock-ho-search-retry.py"
set_option vampire.timeLimit 5

set_option vampire.outputPath "artifacts/ho-search-retry.p" in
theorem native_search_retry (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let first ← IO.FS.readFile "artifacts/ho-search-retry.p.ho-first.stdout"
  let second ← IO.FS.readFile "artifacts/ho-search-retry.p.stdout"
  unless first.contains "GaveUp" && second.contains "--func_ext abstraction" &&
      second.contains "--heur_inst on" && second.contains "--newcnf off" &&
      second.contains "--avatar off" do
    throw <| IO.userError "native retry lost the first outcome or replay settings"
  let limit := (second.splitOn "--time_limit ")[1]!.splitOn " " |>.head!
  unless limit.endsWith "d" do throw <| IO.userError "retry did not use the remaining budget"
  let digits := limit.toList.takeWhile Char.isDigit
  unless (String.ofList digits).toNat! < 50 do
    throw <| IO.userError "native retry restarted its search budget"

-- Disabled and explicit-strategy calls cannot silently select another strategy.
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  fail_if_success vampire [h, hp] (higherOrderSearchRetry := false)
  fail_if_success vampire [h, hp] (strategy := "test-explicit")
  exact h 0 hp

#print axioms native_search_retry

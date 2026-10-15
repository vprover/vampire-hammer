import VampireHammer.Benchmark.Mathlib

open Lean Meta Elab

namespace MathlibBenchmarkTests

theorem original : True := True.intro
theorem indirect : True := original
theorem numberPremise : (0 : Nat) = 0 := rfl
theorem usesNumberPremise : (0 : Nat) = 0 := numberPremise
theorem indirectNumberPremise : (0 : Nat) = 0 := usesNumberPremise

run_elab do
  let premises ← VampireHammer.Benchmark.proofPremises ``usesNumberPremise
  unless premises == #[``numberPremise] do
    throwError "benchmark failed to extract direct non-logic proof premises: {premises}"
  let premises ← VampireHammer.Benchmark.proofPremises ``indirectNumberPremise
  unless premises == #[``usesNumberPremise] do
    throwError "benchmark recursed into the selected premises' proofs: {premises}"
  let logic ← VampireHammer.Benchmark.proofPremises ``indirect
  unless logic.isEmpty do
    throwError "benchmark failed to exclude pure-logic premises"
  let (direct, _, _) ← VampireHammer.Benchmark.auditDependencies (mkConst ``original) ``original
  unless direct do throwError "benchmark failed to detect direct reuse of its target"
  let (indirect, _, _) ← VampireHammer.Benchmark.auditDependencies (mkConst ``indirect) ``original
  unless indirect do throwError "benchmark failed to detect transitive reuse of its target"
  let (independent, axioms, _) ← VampireHammer.Benchmark.auditDependencies (mkConst ``True.intro) ``original
  unless !independent && !axioms.contains ``sorryAx do
    throwError "benchmark rejected an independent proof"

end MathlibBenchmarkTests

-- Replaying this file must not expose the target or the later alias to the tactic.
-- A theorem using a helper introduced by its own command must be excluded.
run_elab do
  let directory := System.FilePath.mk "artifacts/benchmark-replay-tests"
  IO.FS.createDirAll directory
  let source := System.FilePath.mk "Tests/Frontend/BenchmarkReplayFixture.lean"
  let options := (← getOptions).set `maxHeartbeats (65536 : Nat)
  for (target, expected) in #[(`BenchmarkReplayFixture.target, "proved"),
                              (`BenchmarkReplayFixture.excluded, "excluded")] do
    let path := directory / s!"{target}.jsonl"
    IO.FS.writeFile path ""
    withOptions (fun _ => options) <|
      VampireHammer.Benchmark.replayDeclaration target source path.toString
    let events ← (← IO.FS.lines path).mapM fun line => do
      match Lean.Json.parse line with
      | .ok event => pure event
      | .error error => throwError "invalid benchmark event: {error}"
    let some finished := events.find? (fun event =>
        event.getObjValAs? String "event" == .ok "finished")
      | throwError "replay did not finish"
    unless finished.getObjValAs? String "status" == .ok expected do
      throwError "unexpected replay result: {finished.compress}"
    if expected == "proved" then
      unless finished.getObjValAs? Bool "target_in_environment" == .ok false do
        throwError "replay exposed the target to the tactic"
      unless finished.getObjValAs? (Array String) "premises" == .ok #["BenchmarkReplayFixture.premise"] do
        throwError "replay used the wrong premise list"
    else
      unless finished.getObjValAs? String "exclusion_reason" == .ok "same_command_dependency" do
        throwError "replay did not apply the same-command filter"

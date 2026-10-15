import VampireHammer.Export.Process

open VampireHammer.Export.Internal

private def expectFailure (output message : String) : IO Unit := do
  match checkVampireOutcome "artifacts/outcome.p" output "" with
  | .ok () => throw <| IO.userError "unsuccessful search was accepted as a proof"
  | .error error =>
    unless error.contains message do
      throw <| IO.userError s!"expected {message}, got {error}"

private def expectSuccess (output : String) : IO Unit := do
  match checkVampireOutcome "artifacts/outcome.p" output "" with
  | .ok () => pure ()
  | .error error => throw <| IO.userError error

#eval do
  expectFailure "% Termination reason: Time limit\n% Time elapsed: 1.5 s\n" "timed out after 1.5 s"
  -- A worker's instruction limit does not describe the whole portfolio.
  expectFailure "% Termination reason: Instruction limit\n% Time elapsed: 0.014 s\n% Proof not found in time 4.926 s\n% SZS status Timeout for unknown\n"
    "timed out after 4.926 s"
  expectFailure "% SZS status Satisfiable for unknown\n" "SZS status Satisfiable"
  expectFailure "% Termination reason: Refutation not found, incomplete strategy\n" "did not produce a refutation"
  expectFailure "% SZS status GaveUp for unknown\n" "SZS status GaveUp"
  expectFailure "% Aborted by signal SIGABRT on\n% Termination reason: Unknown\n% Termination phase: Initialization\n"
    "Vampire aborted by signal SIGABRT"
  -- Earlier portfolio timeouts must not reject a later successful worker.
  expectSuccess "% Time limit reached!\n% Termination reason: Time limit\n% SZS status Timeout for unknown\n% Termination reason: Refutation\n% SZS status Unsatisfiable for unknown\n"
  expectSuccess "% SZS status Theorem for unknown\n"
  expectSuccess "% SZS status ContradictoryAxioms for unknown\n"
  -- A failed portfolio worker cannot override the final successful worker.
  expectSuccess "% Aborted by signal SIGABRT on\n% Termination reason: Unknown\n% SZS status Theorem for unknown\n"
  -- Saved fixtures need no process summary to carry a valid TSTP proof.
  expectSuccess "tff(final, plain, $false, inference(resolution,[],[a,b])).\n"
  match checkVampireOutcome "artifacts/outcome.p" "" "unknown option" 255 with
  | .ok () => throw <| IO.userError "process failure was accepted as a proof"
  | .error error =>
    unless error.contains "exited with code 255" do
      throw <| IO.userError error

import VampireHammer.Options
import VampireHammer.TFF
import VampireHammer.TSTP
import VampireHammer.Preprocess
import VampireHammer.Export.Diagnostics
import VampireHammer.Export.Processors

/-!
Vampire command construction, durable raw artifacts, timeout reporting, and parsing at the
external process boundary.
-/

namespace VampireHammer.Export.Internal

open Lean Meta Elab Tactic

/-- Read a value from one of Vampire's comment-only summary lines, last
occurrence first.

For example, given `% Termination phase: Saturation`, asking for
`"Termination phase"` returns `some "Saturation"`.  These lines are not TPTP
proof items, so the TPTP parser deliberately discards them.  We inspect them
at the process boundary instead, before trying to decode a proof certificate. -/
private def summaryValue? (reversedLines : List String) (marker : String) : Option String :=
  reversedLines.findSome? fun line =>
    let line := line.trimAscii.toString
    if line.startsWith marker then some (line.drop marker.length).trimAscii.toString else none

/-- The final `% SZS status` of a Vampire run. Portfolio output includes
summaries from unsuccessful workers, so the last status takes precedence. -/
private def szsStatusOfLines? (reversedLines : List String) : Option String :=
  (summaryValue? reversedLines "% SZS status ").bind fun rest => (rest.splitOn " ").head?

/-- The final SZS status reported in `output`. -/
def szsStatus? (output : String) : Option String :=
  szsStatusOfLines? (output.splitOn "\n").reverse

/-- Where the raw output was retained, for error messages. -/
private def savedOutputHint (destination : String) : String :=
  if destination.isEmpty then "Set `vampire.outputPath` to retain the raw Vampire output."
  else s!"Raw output was saved in {destination}.stdout and {destination}.stderr."

/-- Read the final process outcome before parsing a certificate. Portfolio
output includes summaries from unsuccessful workers, so its final SZS status
takes precedence over their timeouts. Comment-only failures are valid TPTP
files, but cannot supply a refutation for replay. An empty `destination`
means the raw output was not retained. -/
def checkVampireOutcome (destination stdout stderr : String) (exitCode : UInt32 := 0) :
    Except String Unit := do
  let lines := (stdout.splitOn "\n" ++ stderr.splitOn "\n").reverse
  let status? := szsStatusOfLines? lines
  if status? == some "Unsatisfiable" || status? == some "Theorem" ||
      status? == some "ContradictoryAxioms" then
    return ()
  let hint := savedOutputHint destination
  if let some signal := summaryValue? lines "% Aborted by signal " then
    throw s!"Vampire aborted by signal {signal}; no complete TSTP proof was produced.\n{hint}"
  let reason? := summaryValue? lines "% Termination reason:"
  let timedOut := status? == some "Timeout" || (status?.isNone && reason? == some "Time limit") ||
    (status?.isNone && reason?.isNone && lines.any (·.contains "% Time limit reached!"))
  if timedOut then
    let elapsed := (summaryValue? lines "% Proof not found in time ").orElse
      (fun _ => summaryValue? lines "% Time elapsed:") |>.getD "an unknown duration"
    let phase := (summaryValue? lines "% Termination phase:").getD "an unknown phase"
    throw s!"Vampire timed out after {elapsed} during {phase}; no complete TSTP proof was produced.\n{hint}"
  if let some status := status? then
    throw s!"Vampire did not produce a refutation (SZS status {status}).\n{hint}"
  if let some reason := reason? then
    unless reason == "Refutation" do
      throw s!"Vampire did not produce a refutation ({reason}).\n{hint}"
  if exitCode != 0 then
    throw s!"Vampire exited with code {exitCode} without a refutation.\n{hint}"

/-- Keep strategy decoding before the fixed replay settings, so command-line
requirements override encoded strategies. Portfolio workers receive the same
requirements through `--forced_options`. Argument order is part of this protocol. -/
private def vampireArguments (opts : Options) (timeLimitMs? : Option Nat := none)
    (alternateHO : Bool := false) : Array String := Id.run do
  let strategy := vampire.strategy.get opts
  let strategyArgs := if strategy.isEmpty then #[] else #["--decode", strategy]
  let higherOrder := vampire.higherOrder.get opts
  let mode := if !higherOrder && strategy.isEmpty && vampire.use_portfolio.get opts then "portfolio" else "vampire"
  let cores := if mode == "portfolio" then Processors.portfolioWorkers opts else 1
  -- `tptp_ac` retains associativity and commutativity steps needed for replay.
  -- AVATAR follows the scheduled strategy unless explicitly disabled.
  let avatarArgs := if higherOrder || vampire.disableAvatar.get opts then #["--avatar", "off"] else #[]
  -- Replay certificates include the target binders selected in AVATAR
  -- splits. Keep the spelling configurable for older custom Vampire builds.
  let avatarSplitCertificateArgs := if vampire.avatarSplitCertificate.get opts then
    #["--proof_extra", vampire.proofExtra.get opts]
  else
    #[]
  -- Scheduled strategies are decoded after the command line; force replay
  -- requirements again inside each worker. Keep the scheduler's slice budgets.
  -- Integrated clausification (`newcnf`) omits the explicit Skolemization
  -- nodes and witness certificates required by replay. Use the classic
  -- clausifier both here and in scheduled workers, including strategies
  -- that encode `newcnf=on`.
  let forcedOptions := "proof=tptp_ac:replay=on:skolemization=syntactic:shuffle_input=off:newcnf=off" ++
    (if higherOrder || vampire.disableAvatar.get opts then ":avatar=off" else "") ++
    (if vampire.avatarSplitCertificate.get opts then ":proof_extra=" ++ vampire.proofExtra.get opts else "")
  let timeLimit := vampire.timeLimit.get opts
  let timeArgument := match timeLimitMs? with
    | some milliseconds => s!"{milliseconds / 100}d"
    | none => toString timeLimit
  -- Decode first so the replay settings and explicit time limit take precedence
  -- over any corresponding options encoded in the strategy. Syntactic
  -- Skolemization retains all enclosing universal variables in scope order,
  -- matching `exists_prenex` and `Classical.skolem` in the Lean backend.
  -- Vampire's standard dependency minimization can instead produce a smaller
  -- function that our current witness construction cannot supply.
  return strategyArgs ++
    #["--mode", mode, "--cores", toString cores, "--shuffle_input", "off",
      "--shuffle_on_schedule_repeats", "off", "--forced_options", forcedOptions,
      "-p", "tptp_ac", "--replay", "on", "--skolemization", "syntactic",
      "--newcnf", "off",
      "--time_limit", timeArgument] ++
    avatarArgs ++ avatarSplitCertificateArgs ++
    (if alternateHO then #["--func_ext", "abstraction", "--pos_ext", "on",
      "--heur_inst", "on", "--cnf_on_the_fly", "conj_eager", "--hol_unif_depth", "4"] else #[])

/-- The configured Vampire, or the package-built one when unset. -/
private def vampireExecutable (opts : Options) : IO String := do
  let configured := vampire.executable.get opts
  if configured.isEmpty then defaultVampireExecutable else pure configured

/-- Whether Lean has asked the current elaboration to stop, e.g. because the
file was edited in the editor. -/
private def elaborationCancelled : CoreM Bool := do
  if ← IO.checkCanceled then return true
  match (← read).cancelTk? with
  | some token => token.isSet
  | none => pure false

/-- Run a process like `IO.Process.output` with `input` on stdin, but poll for
Lean's cancellation and terminate the process then, instead of leaving a
long proof search running after its result is no longer wanted. -/
def outputCancellable (args : IO.Process.SpawnArgs) (input : String) :
    CoreM IO.Process.Output := do
  -- On Unix an exec failure can be reported only by the child (exit 255),
  -- rather than by spawn. Diagnose a missing configured path before forking.
  if args.cmd.contains "/" then
    let executable : System.FilePath := args.cmd
    unless ← executable.pathExists do
      throwError "Could not start Vampire executable `{args.cmd}`: file does not exist"
  let spawned ← (IO.Process.spawn { args with stdout := .piped, stderr := .piped, stdin := .piped }).toBaseIO
  let child ← match spawned with
    | .ok child => pure child
    | .error error => throwError "Could not start Vampire executable `{args.cmd}`: {error}"
  let (stdin, child) ← child.takeStdin
  -- Write from a separate task so that a cancellation is noticed during a
  -- large write too. The handle is closed (EOF) once the task finishes. A
  -- process that exits without reading its input only causes a write error
  -- here, which is ignored: its exit code and output decide the outcome.
  let _ ← IO.asTask (do stdin.putStr input; stdin.flush) .dedicated
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← IO.asTask child.stderr.readToEnd .dedicated
  let mut exitCode? ← child.tryWait
  while exitCode?.isNone do
    if ← elaborationCancelled then
      child.kill
      discard <| child.wait
      throwInterruptException
    IO.sleep 10
    exitCode? ← child.tryWait
  let some exitCode := exitCode? | unreachable!
  pure { exitCode, stdout := ← IO.ofExcept stdout.get, stderr := ← IO.ofExcept stderr.get }

/-- Write one raw artifact beside the configured output path. Nothing is
written when `vampire.outputPath` is empty (the default). -/
def writeArtifact (destination suffix contents : String) : IO Unit := do
  if destination.isEmpty then return
  let path : System.FilePath := destination ++ suffix
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path contents

/-- Whether a finite model building run of at most `deciseconds` shows the
exported abstraction satisfiable. Such a problem has no refutation, so proof
search on it can only time out. Any other result, including a refutation, is
left to the ordinary search. The run's output is retained beside the input
when `vampire.outputPath` is set. -/
def finiteModelExists (query : TFF.Problem) (deciseconds : Nat) : MetaM Bool := do
  -- Vampire's first-order finite-model builder does not support native THF.
  if query.higherOrder then return false
  let opts ← getOptions
  let result ← outputCancellable {
    cmd := ← vampireExecutable opts
    args := #["--mode", "vampire", "--saturation_algorithm", "fmb", "--proof", "off",
      "--time_limit", s!"{deciseconds}d"]
  } (query.text ++ "\n")
  writeArtifact (vampire.outputPath.get opts) ".fmb.stdout" result.stdout
  writeArtifact (vampire.outputPath.get opts) ".fmb.stderr" result.stderr
  writeArtifact (vampire.outputPath.get opts) ".fmb.exitcode" s!"{result.exitCode}\n"
  return szsStatus? result.stdout == some "Satisfiable"

/-- Run Vampire on `query` through stdin and parse the TSTP proof from its
stdout in memory. Concurrent calls therefore never share files.

When `vampire.outputPath` is set, the input and all three process outputs are
also written beside it before parsing: when a decoder or reconstruction rule
fails, the exact proof certificate remains available for inspection and for
creating a deterministic mock test. `satisfiable` is set when Vampire reports
`SZS status Satisfiable`. -/
def invokeVampire (query : TFF.Problem) (satisfiable? : Option (IO.Ref Bool) := none)
    (timeLimitMs? : Option Nat := none) (alternateHO : Bool := false) :
    MetaM Tptp.Data.TptpFile := do
  if let some milliseconds := timeLimitMs? then
    if milliseconds < 100 then throwError "Vampire proof-search budget exhausted"
  let opts ← getOptions
  let destination := vampire.outputPath.get opts
  let input := query.text ++ "\n"
  writeArtifact destination "" input
  Export.diagnosticEvent "exported" [
    ("higher_order", toJson query.higherOrder),
    ("problem_bytes", toJson input.utf8ByteSize),
    ("assertions", toJson query.facts.size)]
  let searchStart ← IO.monoMsNow
  let mut result ← outputCancellable {
    cmd := ← vampireExecutable opts
    args := vampireArguments opts timeLimitMs? alternateHO
  } input
  let total := timeLimitMs?.getD (vampire.timeLimit.get opts * 1000)
  let remaining := total - ((← IO.monoMsNow) - searchStart)
  -- Preserve the ordinary strategy's entire slice. Incomplete saturation can
  -- stop almost immediately; use that otherwise idle time for an alternative.
  -- A finite budget must retain at least one decisecond. Explicit encoded
  -- strategies and first-order inputs retain their requested behavior.
  if query.higherOrder && !alternateHO && vampire.higherOrderSearchRetry.get opts &&
      (vampire.strategy.get opts).isEmpty && szsStatus? result.stdout == some "GaveUp" &&
      (total == 0 || remaining >= 100) then
    writeArtifact destination ".ho-first" input
    writeArtifact destination ".ho-first.stdout" result.stdout
    writeArtifact destination ".ho-first.stderr" result.stderr
    writeArtifact destination ".ho-first.exitcode" s!"{result.exitCode}\n"
    Export.diagnosticEvent "native_search_retry" [
      ("initial_status", toJson (szsStatus? result.stdout)),
      ("remaining_ms", toJson remaining)]
    result ← outputCancellable {
      cmd := ← vampireExecutable opts
      args := vampireArguments opts (if total == 0 then none else some remaining) true
    } input
  writeArtifact destination ".stdout" result.stdout
  writeArtifact destination ".stderr" result.stderr
  writeArtifact destination ".exitcode" s!"{result.exitCode}\n"
  Export.diagnosticEvent "solver_result" [
    ("exit_code", toJson result.exitCode.toNat),
    ("szs_status", toJson (szsStatus? result.stdout)),
    ("termination_reason", toJson (summaryValue? (result.stdout.splitOn "\n").reverse
      "% Termination reason:"))]
  if let some status := szsStatus? result.stdout then
    trace[vampire] "Vampire SZS status {status}"
    if status == "Satisfiable" then
      if let some flag := satisfiable? then flag.set true
  let saved := if destination.isEmpty then "" else
    s!"; raw output saved in {destination}.stdout and {destination}.stderr"
  trace[vampire] "Vampire exited with code {result.exitCode}{saved}"
  -- Process outcomes such as a timeout live in Vampire's comment summary and
  -- are therefore outside the TPTP grammar.  Decode them before parsing;
  -- otherwise a comment-only timeout report looks like an empty proof file.
  match checkVampireOutcome destination result.stdout result.stderr result.exitCode with
  | .ok () => pure ()
  | .error message => throwError "{message}"
  let parserDynlib := vampire.tptpParserDynlib.get opts
  match ← parseVampireTSTPText parserDynlib result.stdout with
  | .ok proof =>
    trace[vampire] "Parsed Vampire TSTP output ({result.stdout.length} characters)"
    match Preprocess.prepare proof with
    | .ok prepared =>
      let .mk inputs := prepared
      trace[vampire] "Preprocessed Vampire proof into {inputs.length} TSTP items"
      pure prepared
    | .error message =>
      throwError "Could not preprocess Vampire TSTP proof: {message}"
  | .error message =>
    throwError "Could not parse Vampire output: {message}\n{savedOutputHint destination}"

/-- Capture TF0 through the configured shell script after the tactic has
restored its state. This preserves the mock protocol used by vampire_export. -/
def captureProblem (query : TFF.Problem) : MetaM Unit := do
  let opts ← getOptions
  let script := vampire.mockScript.get opts
  -- Export always produces a file; fall back to the historical default path.
  let destination := vampire.outputPath.get opts
  let destination := if destination.isEmpty then "artifacts/example.p" else destination
  let result ← IO.Process.output {
    cmd := "/bin/sh"
    args := #[script, destination]
  } (some (query.text ++ "\n"))
  unless result.exitCode == 0 do
    throwError "Mock Vampire failed ({result.exitCode}): {result.stderr}"
  logInfo m!"TPTP problem captured in {destination}"

end VampireHammer.Export.Internal

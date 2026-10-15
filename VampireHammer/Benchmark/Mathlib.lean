import VampireHammer
import Lean.Util.CollectAxioms
import Auto.EvaluateAuto.ConstAnalysis
import Auto.EvaluateAuto.CommandAnalysis

/-! Benchmark commands only. These do not change the hammer or its defaults.
The default strategy supplies only the statement. The separate proof-premise
strategy inspects the original proof only to extract theorem names, as in the
Lean-auto/Duper evaluation; it never supplies the original proof term. -/

namespace VampireHammer.Benchmark

open Lean Meta Elab Command

register_option vampire.benchmarkProver : String := {
  defValue := "vampire-hammer"
  descr := "Benchmark tactic: vampire-hammer, duper, aesop, simp_all or grind"
}
register_option vampire.benchmarkComparison : Bool := {
  defValue := false
  descr := "Load identical baseline imports for every comparison run"
}

initialize benchmarkTactics : IO.Ref (Std.HashMap String (Array Name → TermElabM Term)) ← IO.mkRef {}

/-- Optional baseline imports register their syntax without adding dependencies
to the ordinary hammer benchmark. All comparison runs import the same module. -/
def registerBenchmarkTactic (name : String) (builder : Array Name → TermElabM Term) : IO Unit :=
  benchmarkTactics.modify (·.insert name builder)

private def isTheorem : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

private def appendEvent (path : String) (event : Json) : IO Unit :=
  IO.FS.withFile path .append fun stream => do
    stream.putStrLn event.compress
    stream.flush

private def writeCatalog (path : String) (humanOnly : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut rows := #[]
  for (name, info) in env.constants.toList do
    unless isTheorem info && !name.isInternalDetail && name.toString.toName == name do continue
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := modules[index.toNat]!.toString
    unless moduleName.startsWith "Mathlib." do continue
    if humanOnly && !(← liftCoreM <| EvalAuto.Name.isHumanTheorem name) then continue
    rows := rows.push <| (Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName),
      ("catalog_strategy", toJson (if humanOnly then "duper-style" else "hammer")),
      ("type_size", toJson info.type.sizeWithoutSharing)]).compress
  IO.FS.writeFile path (String.intercalate "\n" rows.toList ++ "\n")

elab "hammer_mathlib_catalog " path:str : command => writeCatalog path.getString false
elab "hammer_mathlib_proof_catalog " path:str : command => writeCatalog path.getString true

/-- Direct theorem dependencies, excluding pure logic as in EvalAuto.useAuto.
This deliberately does not recurse into proofs of the selected premises. -/
private def proofPremisesOf (info : ConstantInfo) : CoreM (Array Name) := do
  let some proof := info.value? (allowOpaque := true)
    | throwError "benchmark target has no proof"
  let names ← EvalAuto.Expr.getUsedTheorems proof
  let names ← names.filterM fun name => do
    return name != info.name && !(← EvalAuto.Name.onlyLogicInType name)
  return names.qsort (fun a b => a.toString < b.toString)

def proofPremises (target : Name) : CoreM (Array Name) := do
  proofPremisesOf (← getConstInfo target)

elab "hammer_mathlib_statements " selection:str " to " output:str : command => do
  let text ← IO.FS.readFile selection.getString
  let mut rows := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    let info ← getConstInfo line.toName
    let statement ← liftTermElabM <| withOptions (fun opts =>
        (opts.setBool `pp.universes true).set `pp.width (100 : Nat)) do
      return (← ppExpr info.type).pretty
    rows := rows.push <| (Json.mkObj [
      ("name", toJson line), ("universes", toJson (info.levelParams.map Name.toString)),
      ("statement", toJson statement), ("type_size", toJson info.type.sizeWithoutSharing)]).compress
  IO.FS.writeFile output.getString (String.intercalate "\n" rows.toList ++ "\n")

/-- Follow proof dependencies through imported declarations, so aliases or
automatically selected lemmas cannot indirectly reuse the target theorem. -/
def auditDependencies (proof : Expr) (target : Name) :
    CoreM (Bool × Array Name × Nat) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut pending := proof.getUsedConstants
  let mut axioms := #[]
  let mut reusesTarget := false
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == target then reusesTarget := true
    if let some info := env.find? name then
      if info.isAxiom then axioms := axioms.push name
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  return (reusesTarget, axioms, seen.size)

private def tryTheorem (target : Name) (path : String) (useProofPremises : Bool)
    (original? : Option ConstantInfo := none) : TermElabM Unit := do
  let start ← IO.monoNanosNow
  appendEvent path <| Json.mkObj [
    ("event", toJson "started"), ("name", toJson target.toString),
    ("monotonic_ns", toJson start)]
  let saved ← Term.saveState
  let prover := vampire.benchmarkProver.get (← getOptions)
  let selected ← IO.mkRef (#[] : Array Name)
  let attempt : TermElabM Unit := do
    let info ← match original? with
      | some info => pure info
      | none => getConstInfo target
    unless isTheorem info do throwError "benchmark target is not a theorem"
    let premises ← if useProofPremises then proofPremisesOf info else pure #[]
    selected.set premises
    let tactic : Term ← if prover != "vampire-hammer" then do
      let some builder := (← benchmarkTactics.get)[prover]?
        | throwError "benchmark prover {prover} is not registered; import VampireHammer.Benchmark.Comparison"
      builder premises
    else if useProofPremises then do
      let terms : Array Term := premises.map (fun name => ⟨mkIdent name⟩)
      let hints ← terms.mapM (fun term => `(Auto.hintelem| $term:term))
      let hints := #[(← `(Auto.hintelem| *))] ++ hints
      `(term| by intros; vampire [$[$hints],*])
    else
      `(term| by vampire)
    appendEvent path <| Json.mkObj [
      ("event", toJson "premises"), ("name", toJson target.toString),
      ("evaluation_strategy", toJson (if useProofPremises then "duper-style" else "hammer")),
      ("premises", toJson (premises.map Name.toString))]
    let proofStart ← IO.monoNanosNow
    let heartbeatStart ← IO.getNumHeartbeats
    let fresh := `MathlibHammerBenchmark.proof
    let proof ← Term.withoutErrToSorry <| Term.withDeclName fresh <| withReader (fun context =>
        { context with declName? := some target }) <| Term.withLevelNames info.levelParams do
      -- This also makes the existing premise selector exclude the target.
      let proof ← Term.elabTermEnsuringType tactic info.type
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      if proof.hasMVar then throwError "benchmark proof has unresolved metavariables"
      return proof
    -- `addDecl` submits the reconstructed value to Lean's kernel.
    addDecl <| .thmDecl {
      name := fresh, levelParams := info.levelParams, type := info.type, value := proof }
    let proofEnd ← IO.monoNanosNow
    appendEvent path <| Json.mkObj [
      ("event", toJson "proof_checked"), ("name", toJson target.toString),
      ("seconds", toJson ((proofEnd - start).toFloat / 1000000000))]
    let heartbeatEnd ← IO.getNumHeartbeats
    let (reusesTarget, axioms, dependencies) ← if useProofPremises then
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 0 }) <| auditDependencies proof target
    else
      auditDependencies proof target
    let hasSorry := axioms.contains ``sorryAx
    let reconstructionModes := VampireHammer.Replay.reconstructionModes proof
    let route := if prover != "vampire-hammer" then prover else
      if reconstructionModes.isEmpty then "direct" else "vampire"
    let status := if hasSorry then "sorry" else if reusesTarget then "reuses_target" else "proved"
    let endTime ← IO.monoNanosNow
    let seconds := (if useProofPremises then proofEnd - start else endTime - start).toFloat / 1000000000
    appendEvent path <| Json.mkObj [
      ("event", toJson "finished"), ("name", toJson target.toString),
      ("status", toJson status), ("seconds", toJson seconds),
      ("prover", toJson prover),
      ("route", toJson route), ("route_source", toJson "accepted_proof"),
      ("reconstruction_modes", toJson reconstructionModes),
      ("evaluation_strategy", toJson (if useProofPremises then "duper-style" else "hammer")),
      ("premise_count", toJson premises.size), ("premises", toJson (premises.map Name.toString)),
      ("heartbeats_raw", toJson (heartbeatEnd - heartbeatStart)),
      ("target_in_environment", toJson (original?.isNone)),
      ("setup_seconds", toJson ((proofStart - start).toFloat / 1000000000)),
      ("audit_seconds", toJson ((endTime - proofEnd).toFloat / 1000000000)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("dependency_count", toJson dependencies), ("kernel_checked", toJson true),
      ("reuses_target", toJson reusesTarget)]
    saved.restore
  let failed (error : Exception) : TermElabM Unit := do
    let message ← error.toMessageData.toString
    let seconds := ((← IO.monoNanosNow) - start).toFloat / 1000000000
    saved.restore
    appendEvent path <| Json.mkObj [
      ("event", toJson "finished"), ("name", toJson target.toString),
      ("status", toJson "error"), ("seconds", toJson seconds),
      ("prover", toJson prover),
      ("premises", toJson ((← selected.get).map Name.toString)),
      ("error", toJson message), ("kernel_checked", toJson false)]
  -- `try` does not catch heartbeat or recursion limits. Under the proof-premise
  -- strategy these are ordinary failures of this theorem, not of the replay.
  if useProofPremises then tryCatchRuntimeEx attempt failed else tryCatch attempt failed

/-- Loading environment extensions runs the imported modules' initializers,
as the `lean` executable itself does for every file. -/
@[implemented_by enableInitializersExecution]
private opaque enableInitializers : BaseIO Unit

/-- Options from Mathlib's `leanOptions` that affect elaboration; the replayed
files are elaborated with them by Mathlib's own build. -/
private def mathlibOptions : Options :=
  ({} : Options).set `maxSynthPendingDepth (3 : Nat) |>.set `autoImplicit false

/-- Import a `module` file's dependencies as Lean does for that file, plus the
benchmark module. Module files elaborate differently from ordinary ones
(auto-params, `to_additive`, private names), so they are replayed as modules.
Lean refuses a non-`module` import of a module once all imports are loaded;
the benchmark module is imported anyway, as `meta` so that its tactics can be
evaluated. Only the exposed data of the imports is loaded, as for the module
itself: with all data, Mathlib's own proofs see definitions they were written
against as opaque and fail. The modules imported by this process (`initialized`) already ran
their initializers: imported into a module, the native initializers of
non-module code are not found and would be interpreted a second time. -/
private def importAsModule (imports : Array Import) (benchmarkModule mainModule : Name)
    (initialized : Array Name) : IO Environment := do
  interpretedModInits.modify fun done => initialized.foldl (·.insert ·) done
  let imports := imports.push { module := benchmarkModule, isMeta := true }
  let env ← withImporting do
    let state ← IO.mkRef (default : ImportState)
    try ReaderT.run (importModulesCore imports (globalLevel := .exported)) state
    catch error =>
      unless (toString error).startsWith "cannot import non-`module`" do throw error
    finalizeImport (← state.get) imports {} (leakEnv := false) (loadExts := true)
      (level := .exported) (isModule := true)
  return env.setMainModule mainModule

/-- Re-elaborate the defining file and test each target in the environment
immediately before the command that created it, following EvalAuto's setup 2.
The file is replayed once for all targets; replay continues after each proof
attempt from the untouched state after the target's command. The callback sees
the new ConstantInfo only as benchmark metadata. With `asModule`, a `module`
file is replayed as one (see `importAsModule`). Returns the targets that could
not be attempted, with the reason. -/
def replayDeclarations (targets : Array Name) (sourceFile : System.FilePath) (path : String)
    (mainModule : Name := .anonymous) (asModule := false) : CoreM (Array (Name × String)) := do
  let options ← getOptions
  let input ← IO.FS.readFile sourceFile
  let inputCtx := Parser.mkInputContext input sourceFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- Unlike EvalAuto.processHeaderEnsuring, load environment extensions
  -- (instances, namespaces, notation) as Lean's own frontend does. The main
  -- module keeps private names identical to those in the original proof.
  enableInitializers
  let benchmarkModule := if vampire.benchmarkProver.get options == "vampire-hammer" &&
      !(options.getBool `vampire.benchmarkComparison false) then
    `VampireHammer.Benchmark.Mathlib
  else
    `VampireHammer.Benchmark.Comparison
  let asModule := asModule && Elab.HeaderSyntax.isModule header
  let (env, messages) ← if asModule then
      let initialized := (← getEnv).header.moduleNames
      pure (← importAsModule (Elab.headerToImports header) benchmarkModule mainModule initialized,
        messages)
    else
      Elab.processHeaderCore (header.raw.getPos?.getD 0) (isModule := false)
        (Elab.headerToImports header ++ #[{ module := benchmarkModule }])
        {} messages inputCtx (mainModule := mainModule)
  if messages.hasErrors then
    let reason := s!"benchmark could not import the replayed module's dependencies: \
      {← messages.toList.mapM fun message => message.data.toString}"
    return targets.map (·, reason)
  let replayStart ← IO.monoNanosNow
  for target in targets do
    appendEvent path <| Json.mkObj [
      ("event", toJson "replay_started"), ("name", toJson target.toString),
      ("source_file", toJson sourceFile.toString)]
  let replayOptions := if asModule then mathlibOptions else {}
  let replayOptions := if options.getBool `vampire.benchmarkComparison false then
    replayOptions.set `maxHeartbeats (0 : Nat)
      |>.set `synthInstance.maxHeartbeats (0 : Nat)
  else
    replayOptions
  let commandState := Command.mkState env messages replayOptions
  -- Time spent in proof attempts is not replay time of later targets.
  let attemptNanos ← IO.mkRef (0 : Nat)
  let action (target : Name) (before after : Elab.Frontend.State)
      (info : ConstantInfo) : IO Unit := do
    if after.commandState.messages.hasErrors then
      let errors ← (after.commandState.messages.toList.filter (·.severity == .error)).take 3
        |>.mapM fun (message : Message) => return s!"{message.pos}: {← message.data.toString}"
      throw <| IO.userError s!"benchmark source replay produced elaboration errors: {errors}"
    let previous := before.commandState.env
    let some originalProof := info.value? (allowOpaque := true)
      | throw <| IO.userError "replayed theorem has no proof"
    let unknown := (originalProof.getUsedConstants ++ info.type.getUsedConstants).filter
      (fun name => (previous.find? name).isNone)
    let replayEnd ← IO.monoNanosNow
    let replayNanos := replayEnd - replayStart - (← attemptNanos.get)
    let replaySeconds := replayNanos.toFloat / 1000000000
    appendEvent path <| Json.mkObj [
      ("event", toJson "replay_finished"), ("name", toJson target.toString),
      ("replay_seconds", toJson replaySeconds), ("target_in_environment", toJson ((previous.find? target).isSome))]
    if !unknown.isEmpty then
      appendEvent path <| Json.mkObj [
        ("event", toJson "finished"), ("name", toJson target.toString),
        ("status", toJson "excluded"), ("exclusion_reason", toJson "same_command_dependency"),
        ("unavailable_constants", toJson (unknown.map Name.toString)),
        ("replay_seconds", toJson replaySeconds), ("kernel_checked", toJson false)]
      return
    if (previous.find? target).isSome then
      throw <| IO.userError "target theorem unexpectedly exists before its declaration"
    let run : CoreM Unit := do
      (Term.TermElabM.run' <| tryTheorem target path true (some info)).run'
    -- In a batch, target `i` writes its problems next to the configured
    -- output as `{i:05d}.p`, so their diagnostics stay separate.
    let outputPath := vampire.outputPath.get options
    let options := if targets.size > 1 && !outputPath.isEmpty then
        let index := (targets.idxOf? target).getD 0
        let digits := toString index
        let name := String.mk (List.replicate (5 - digits.length) '0') ++ digits ++ ".p"
        options.set `vampire.outputPath
          (((System.FilePath.mk outputPath).parent.getD ".") / name).toString
      else options
    -- `diagnosticCase` is set by the generated batch command to its first
    -- target.  Give every replayed theorem its own identity before it emits
    -- durable/live Vampire events, so collectors can attribute routed-query
    -- diagnostics even when one Lean invocation proves several targets.
    let options := options.set `vampire.diagnosticCase target.toString
    let (_, _) ← run.toIO
      { fileName := sourceFile.toString, fileMap := inputCtx.fileMap, options }
      { env := previous }
    attemptNanos.modify (· + ((← IO.monoNanosNow) - replayEnd))
  -- Current Lean stores declarations asynchronously; EvalAuto's old map₂
  -- difference misses them. find? waits for the target's declaration task.
  -- Each command starts with an empty message log, so keep the first errors.
  let errors ← IO.mkRef (#[] : Array String)
  let failures ← IO.mkRef (#[] : Array (Name × String))
  let replay : Elab.Frontend.FrontendM (Array Name) := do
    let mut pending := targets
    let mut done := false
    while !done && !pending.isEmpty do
      let before ← get
      done ← Elab.Frontend.processCommand
      let after ← get
      for message in after.commandState.messages.toList do
        if message.severity == .error && (← errors.get).size < 5 then
          errors.modify (·.push s!"{message.pos}: {← message.data.toString}")
      for target in pending do
        if (before.commandState.env.find? target).isNone then
          if let some info := after.commandState.env.find? target then
            pending := pending.filter (· != target)
            try action target before after info
            catch error => failures.modify (·.push (target, toString error))
    return pending
  let (missing, _) ← (replay { inputCtx }).run
    { commandState, parserState, cmdPos := parserState.pos }
  let reason := s!"target theorem was not reproduced when replaying its defining file: {← errors.get}"
  return (← failures.get) ++ missing.map (·, reason)

/-- `replayDeclarations` for one target; a target that could not be attempted
is an error. -/
def replayDeclaration (target : Name) (sourceFile : System.FilePath) (path : String)
    (mainModule : Name := .anonymous) (asModule := false) : CoreM Unit := do
  if let some (_, reason) := (← replayDeclarations #[target] sourceFile path mainModule asModule)[0]? then
    throwError reason

/-- Whether a replay error is an elaboration failure of the defining file. -/
private def replayFailed (message : String) : Bool :=
  message.startsWith "benchmark source replay produced elaboration errors" ||
    message.startsWith "target theorem was not reproduced"

private def tryReplayedTheorem (target : Name) (path : String)
    (definingModule? : Option Name := none) : CoreM Unit := do
  try
    let moduleName? ← match definingModule? with
      | some moduleName => pure (some moduleName)
      | none => findModuleOf? target
    let some moduleName := moduleName?
      | throwError "cannot find the defining module of {target}"
    let some uri ← Server.documentUriFromModule? moduleName
      | throwError "cannot locate source for {moduleName}"
    let some sourceFile := System.Uri.fileUriToPath? uri
      | throwError "source URI for {moduleName} is not a file"
    -- Source replay has its own process limit; the per-proof heartbeat limit
    -- is reset in the fresh Core context created by replayDeclaration.
    -- Mathlib files are `module`s, but the benchmark module is not, so they
    -- are replayed as ordinary files, where the hammer sees all data. Some
    -- proofs elaborate only as modules; those files are replayed again so.
    withReader (fun ctx => { ctx with maxHeartbeats := 0 }) <|
      tryCatch (replayDeclaration target sourceFile.normalize path moduleName) fun error => do
        let message ← error.toMessageData.toString
        unless replayFailed message do throw error
        replayDeclaration target sourceFile.normalize path moduleName (asModule := true)
  catch error =>
    appendEvent path <| Json.mkObj [
      ("event", toJson "finished"), ("name", toJson target.toString),
      ("status", toJson "infrastructure_error"), ("kernel_checked", toJson false),
      ("error", toJson (← error.toMessageData.toString))]

/-- Several targets of one defining module, replayed together. Targets whose
file elaborates only as a module are replayed again so (see
`tryReplayedTheorem`); the rest that could not be attempted are recorded as
infrastructure errors. -/
private def tryReplayedTheorems (targets : Array Name) (moduleName : Name) (path : String) :
    CoreM Unit := do
  let recordFailures (failures : Array (Name × String)) : CoreM Unit :=
    for (target, reason) in failures do
      appendEvent path <| Json.mkObj [
        ("event", toJson "finished"), ("name", toJson target.toString),
        ("status", toJson "infrastructure_error"), ("kernel_checked", toJson false),
        ("error", toJson reason)]
  try
    let some uri ← Server.documentUriFromModule? moduleName
      | throwError "cannot locate source for {moduleName}"
    let some sourceFile := System.Uri.fileUriToPath? uri
      | throwError "source URI for {moduleName} is not a file"
    withReader (fun ctx => { ctx with maxHeartbeats := 0 }) do
      let failures ← replayDeclarations targets sourceFile.normalize path moduleName
      let retry := failures.filter (replayFailed ·.2)
      recordFailures (failures.filter (!replayFailed ·.2))
      unless retry.isEmpty do
        recordFailures (← replayDeclarations (retry.map (·.1)) sourceFile.normalize path moduleName
          (asModule := true))
  catch error =>
    let reason ← error.toMessageData.toString
    recordFailures (targets.map (·, reason))

elab "hammer_mathlib_try " declaration:str " recording " path:str : command =>
  liftTermElabM <| tryTheorem declaration.getString.toName path.getString false

elab "hammer_mathlib_try_with_premises " declaration:str " recording " path:str : command =>
  liftCoreM <| tryReplayedTheorem declaration.getString.toName path.getString

/-- Catalog metadata lets declaration replay locate the source without first
importing all of Mathlib. The proof still uses the original file's imports and
the environment immediately before its declaration. -/
elab "hammer_mathlib_try_with_premises_in_module " declaration:str " module " moduleName:str
    " recording " path:str : command =>
  liftCoreM <| tryReplayedTheorem declaration.getString.toName path.getString
    (some moduleName.getString.toName)

/-- Replay a defining file once for several targets (space-separated names). -/
elab "hammer_mathlib_try_batch_in_module " declarations:str " module " moduleName:str
    " recording " path:str : command =>
  liftCoreM <| tryReplayedTheorems
    ((declarations.getString.splitOn " ").filter (!·.isEmpty) |>.map String.toName |>.toArray)
    moduleName.getString.toName path.getString

end VampireHammer.Benchmark

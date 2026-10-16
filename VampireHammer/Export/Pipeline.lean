import VampireHammer.Export.Problem
import VampireHammer.Export.Process
import VampireHammer.Export.Routing
import VampireHammer.Export.Parallel
import VampireHammer.Replay
import VampireHammer.FactReporting

/-!
The capture pipeline: checked source rewriting and monomorphization, reification, TF0 export,
Vampire, and replay.
-/

namespace VampireHammer.Export.Internal

open Lean Meta Elab Tactic

/-- Marker raised when the first-order monomorphization heartbeat window is
exhausted; `replayWithMonoFallback` retries such failures natively
higher-order. -/
private def monoDeadlineMarker : String :=
  "first-order monomorphization heartbeat window exhausted"

/-- Whether a failure reports the first-order monomorphization window. -/
def isMonoDeadline (message : String) : Bool :=
  message.contains monoDeadlineMarker

/-- Window the first-order monomorphization of the default route. Native
higher-order routes are not windowed. Export/search/replay continuations
restore the caller's limits, including after an unsupported-translation retry.
A blown window restores the entry state transactionally and raises the marker so the
caller can abandon the attempt before the export. The window never exceeds the
caller's remaining heartbeats. An optional shared budget counts raw heartbeats
across branch monomorphizations, excluding export/search/replay continuations. -/
def withMonoDeadline (action : (MetaM α → MetaM α) → MetaM α)
    (sharedBudget? : Option (IO.Ref Nat) := none) : MetaM α := do
  let options ← getOptions
  let window := vampire.monoHeartbeats.get options
  if window == 0 || vampire.higherOrder.get options then return ← action id
  Core.checkMaxHeartbeats "first-order monomorphization"
  let start ← IO.getNumHeartbeats
  let context ← readThe Core.Context
  let remaining ← sharedBudget?.mapM (·.get)
  let window := min (window * 1000) (remaining.getD (window * 1000))
  let allowance := if context.maxHeartbeats == 0 then window else
    min window (context.initHeartbeats + context.maxHeartbeats - start)
  if allowance == 0 then throwError monoDeadlineMarker
  let saved ← saveState
  let continuationTimedOut ← IO.mkRef false
  let continuationHeartbeats ← IO.mkRef 0
  let resume (continuation : MetaM α) : MetaM α := do
    Core.checkSystem "first-order monomorphization"
    -- Preserve the live monomorphization context, but restore the caller's
    -- resource limits before export, search and reconstruction.
    let continuationStart ← IO.getNumHeartbeats
    try
      withTheReader Core.Context (fun current =>
        { current with initHeartbeats := context.initHeartbeats, maxHeartbeats := context.maxHeartbeats }) <|
        withOptions (fun current => current.set `synthInstance.maxHeartbeats
          (synthInstance.maxHeartbeats.get options)) <|
          tryCatchRuntimeEx continuation fun error => do
            if error.isMaxHeartbeat then continuationTimedOut.set true
            throw error
    finally
      continuationHeartbeats.modify (· + ((← IO.getNumHeartbeats) - continuationStart))
  try
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun current =>
        { current with initHeartbeats := start, maxHeartbeats := allowance }) <|
        withOptions (fun current =>
          let synthesis := synthInstance.maxHeartbeats.get current
          let cap := max 1 (allowance / 1000)
          current.set `synthInstance.maxHeartbeats
            (if synthesis == 0 then cap else min synthesis cap)) (action resume))
      fun error => do
        if (← continuationTimedOut.get) || !error.isMaxHeartbeat then throw error
        saved.restore
        Core.checkInterrupted
        Core.checkMaxHeartbeats "first-order monomorphization"
        throwError monoDeadlineMarker
  finally
    if let some budget := sharedBudget? then
      budget.modify (· - ((← IO.getNumHeartbeats) - start - (← continuationHeartbeats.get)))

/-- Run monomorphization once, export and call Vampire, reconstruct a closed
proof over a local TPTP signature, and finally instantiate that proof through
`Lam2DAAF`. Dedicated rules construct proof terms; only unsupported derived
rules use the isolated `grind` fallback. -/
private def replayVampireOnce (lemmas inhs : Array Auto.Lemma)
    (searchBudget : IO.Ref Nat) (satisfiable : IO.Ref Bool)
    (monoBudget? : Option (IO.Ref Nat) := none) : MetaM Expr := do
  let originalContext ← getLCtx
  let strategy ← IO.mkRef (none : Option String)
  let (proof, _) ← withMonoDeadline (fun resume =>
    monomorphizeWithOptionalFacts lemmas inhs (fun state => resume <| (@id (Auto.Reif.ReifM Expr) do
    let state ← get
    let maxLevel ← Auto.computeMaxLevel state.facts
    (do
      let (problem, exportFacts) ← prepareFirstOrderProblem state.facts state.inhTys state.inds
      let exportInhs := (← Auto.LamReif.getRst).nonemptyMap.toArray.map
        (fun (sort, _) => Auto.Embedding.Lam.REntry.nonempty sort)
      let parsed ← liftM <| (show MetaM Tptp.Data.TptpFile from do
        let remaining ← searchBudget.get
        let unlimited := vampire.timeLimit.get (← getOptions) == 0
        let seconds := if unlimited then 0 else remaining / 1000
        if !unlimited && seconds == 0 then throwError "Vampire proof-search budget exhausted"
        let searchStart ← IO.monoMsNow
        try
          let precheck := vampire.satPrecheck.get (← getOptions)
          if precheck != 0 && (unlimited || precheck < 10 * seconds) then
            if ← finiteModelExists problem precheck then
              satisfiable.set true
              let destination := vampire.outputPath.get (← getOptions)
              writeArtifact destination "" (problem.text ++ "\n")
              let saved := if destination.isEmpty then "" else
                s!"\nFinite model building output was saved in {destination}.fmb.stdout."
              throwError "Vampire did not produce a refutation (SZS status Satisfiable).{saved}"
          withOptions (fun options => options.set `vampire.timeLimit seconds) <|
            do
              let (parsed, found) ← invokeVampireStrategy problem satisfiable
              strategy.set found
              pure parsed
        finally
          let elapsed := (← IO.monoMsNow) - searchStart
          searchBudget.modify (· - elapsed))
      let decoded ← match Replay.decodeSteps problem parsed with
        | .ok decoded => pure decoded
        | .error message => throwError "Could not decode Vampire TPTP proof: {message}"
      let _ ← liftM <| (show MetaM Unit from do
        trace[vampire] "Decoded {decoded.steps.size} Vampire proof steps and {decoded.derivedSymbols.size} proof-local symbols into lean-auto LamTerms")
      let proof ← Replay.replay problem decoded exportInhs exportFacts
      let proof ← liftM <| closeMonomorphizationProof originalContext proof
      pure (FactReporting.markStrategy (← strategy.get) (Replay.markReconstruction problem.higherOrder proof))
      : Auto.LamReif.ReifM Expr).run' {u := maxLevel}) state)) monoBudget?
  pure proof


private partial def derivesOnlyFromStructureLaws : Auto.DTr → Bool
  | .leaf label => label.startsWith structureLawLabel
  | .node _ premises => !premises.isEmpty && premises.all derivesOnlyFromStructureLaws

/-- Adding optional record laws can change Auto's specialization and simplify
away definitions needed by the existing object encoding. If the strengthened
export is satisfiable, retry without the new record laws. Both searches share
the configured budget; timeout, decoding and replay errors are propagated.
Preserve the first query and raw outcome for diagnosis. -/
private def replayWithRecordLawRetry (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat) := none)
    (monoBudget? : Option (IO.Ref Nat) := none) : MetaM Expr := do
  let original := lemmas.filter fun fact => !derivesOnlyFromStructureLaws fact.deriv
  let limit := vampire.timeLimit.get (← getOptions)
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (limit * 1000)
  let saved ← saveState
  let satisfiable ← IO.mkRef false
  try
    replayVampireOnce lemmas inhs budget satisfiable monoBudget?
  catch error =>
    unless original.size < lemmas.size && (← satisfiable.get) &&
        (limit == 0 || (← budget.get) >= 1000) do throw error
    saved.restore
    let destination := vampire.outputPath.get (← getOptions)
    unless destination.isEmpty do
      for suffix in ["", ".stdout", ".stderr", ".exitcode", ".fmb.stdout"] do
        let source : System.FilePath := destination ++ suffix
        if ← source.pathExists then
          IO.FS.rename source (destination ++ ".with-record-laws" ++ suffix)
    trace[vampire] "Retrying satisfiable strengthened export without {lemmas.size - original.size} ordinary record laws"
    replayVampireOnce original inhs budget (← IO.mkRef false) monoBudget?

/-- Preserve any completed FO artifacts before the mono-deadline HO retry. -/
def preserveBeforeMonoHigherOrder : MetaM Unit := do
  let destination := vampire.outputPath.get (← getOptions)
  unless destination.isEmpty do
    for suffix in ["", ".stdout", ".stderr", ".exitcode", ".fmb.stdout"] do
      let source : System.FilePath := destination ++ suffix
      if ← source.pathExists then
        IO.FS.rename source (destination ++ ".before-ho" ++ suffix)

/-- First-order search with a heartbeat window on monomorphization. A blown
window abandons the attempt before the export and retries the proof natively
higher-order with specialization saturation skipped. This can reduce mono
work, but can also omit dependent or type-polymorphic premise instances. Both
attempts share one search budget; every other
failure propagates unchanged. -/
private def replayWithMonoFallback (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat))
    (deferMonoFallback : Bool) (monoBudget? : Option (IO.Ref Nat)) : MetaM Expr := do
  let limit := vampire.timeLimit.get (← getOptions)
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (limit * 1000)
  let saved ← saveState
  try
    return ← replayWithRecordLawRetry lemmas inhs (some budget) monoBudget?
  catch error =>
    let message ← error.toMessageData.toString
    unless !deferMonoFallback && isMonoDeadline message && (limit == 0 || (← budget.get) >= 1000) do throw error
    saved.restore
    preserveBeforeMonoHigherOrder
    trace[vampire] "Retrying monomorphization heartbeat failure natively higher-order without saturation: {message}"
    withOptions (fun options => options.set `vampire.higherOrder true |>.set `vampire.strategy ""
      |>.set `auto.mono.saturationThreshold 0) <|
      replayWithRecordLawRetry lemmas inhs (some budget)

/-- Whether the tactic's deferred-inhabitant recovery (`withDeferredWitness`)
will repair this failure by retrying the whole problem. A representation switch
must not preempt it. With `vampire.deferInhabitants` off, the first-order
object encoding is the intended answer to a missing domain. -/
private def deferredRecoveryApplies (error : Exception) : CoreM Bool := do
  return vampire.deferInhabitants.get (← getOptions) &&
    (Export.missingDomainType? error.toMessageData).isSome

/-- Only failures specific to export or the external proof route warrant a
different encoding. Source elaboration and monomorphization are shared. -/
private def canRetryFirstOrder (message : String) : Bool :=
  message.startsWith "THF export:" ||
  message.startsWith "Vampire timed out" ||
  message.startsWith "Vampire did not produce a refutation" ||
  message.startsWith "Vampire aborted" ||
  message.startsWith "Could not decode Vampire TPTP proof:" ||
  message.startsWith "Could not parse Vampire output:" ||
  message.startsWith "Vampire replay retained an unbound temporary variable"

/-- A prepared input retains its exact reification valuation and temporary
local context for checked replay. It is never re-exported after search. -/
private structure PreparedQuery where
  problem : TFF.Problem
  replay : Tptp.Data.TptpFile → MetaM Expr

/-- Prepare the representation selected by the current options from an
already monomorphized state; the caller restores the state between routes. -/
private def preparedFromState (originalContext : LocalContext) :
    Auto.Reif.ReifM PreparedQuery := do
  let state ← get
  let u ← Auto.computeMaxLevel state.facts
  (do
    let (problem, facts) ← prepareFirstOrderProblem state.facts state.inhTys state.inds
    let inhs := (← Auto.LamReif.getRst).nonemptyMap.toArray.map
      (fun (sort, _) => Auto.Embedding.Lam.REntry.nonempty sort)
    let context ← liftM (show MetaM Meta.Context from read)
    let lamState ← get
    let reifState ← liftM (show Auto.Reif.ReifM Auto.Reif.State from get)
    let replay := fun parsed => withReader (fun _ => context) do
      let decoded ← match Replay.decodeSteps problem parsed with
        | .ok decoded => pure decoded
        | .error message => throwError "Could not decode Vampire TPTP proof: {message}"
      let proof ← ((Replay.replay problem decoded inhs facts).run' lamState).run' reifState
      let proof ← closeMonomorphizationProof originalContext proof
      return Replay.markReconstruction problem.higherOrder proof
    pure { problem, replay }
    : Auto.LamReif.ReifM PreparedQuery).run' {u}

private def prepareQuery (lemmas inhs : Array Auto.Lemma) : MetaM PreparedQuery := do
  let originalContext ← getLCtx
  let (prepared, _) ← monomorphizeWithOptionalFacts lemmas inhs (preparedFromState originalContext)
  return prepared

/-- A dedicated thread also runs with `lean -j1`. Split fresh-name generators,
propagate cancellation and restore the task's complete state only if HO is used. -/
private def prepareQueryAsync (action : MetaM PreparedQuery) :
    MetaM (BaseIO Unit × Task (Except Exception (PreparedQuery × Core.State × Meta.State))) := do
  let context ← read
  let state ← get
  let token ← IO.CancelToken.new
  let wrapped ← Core.wrapAsync (fun () => do
    let (prepared, metaState) ← action.run context state
    return (prepared, ← get, metaState)) (some token)
  if let some parent := (← readThe Core.Context).cancelTk? then parent.onSet token.set
  let task ← (wrapped ()).asTask .dedicated
  return (token.set, task)

private def chargeSearch (budget : IO.Ref Nat) (action : MetaM α) : MetaM α := do
  let start ← IO.monoMsNow
  try
    action
  finally
    budget.modify (· - ((← IO.monoMsNow) - start))

/-- Opt-in staged search. Percentages are of the budget on entry; unused time
passes to HO. Model building only rules out a refutation of the FO abstraction,
so a finite model skips FO search rather than aborting the HO attempt. -/
private def replayStaged (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat)) : MetaM Expr := do
  let options ← getOptions
  let limit := vampire.timeLimit.get options
  if limit == 0 then throwError "internal staged search requires a finite positive timeLimit"
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (limit * 1000)
  let total ← budget.get
  let destination := vampire.outputPath.get options
  let foDestination := if destination.isEmpty then "" else destination ++ ".fo.p"
  let hoOptions := fun opts : Options => opts.set `vampire.higherOrder true
  let foOptions := fun opts : Options => opts.set `vampire.higherOrder false |>.set `vampire.strategy ""
  let prepareHO := withOptions hoOptions do
    let prepared ← prepareQuery lemmas inhs
    return prepared
  let background? ← if InternalSearch.prepareAsync options then
    pure (some (← prepareQueryAsync prepareHO)) else pure none
  let saved ← saveState
  try
    (do
      try
        withOptions (fun opts => (foOptions opts).set `vampire.outputPath foDestination) do
          let prepared ← prepareQuery lemmas inhs
          writeArtifact foDestination "" (prepared.problem.text ++ "\n")
          let precheck := min (← budget.get) (total * 5 / 100) / 100
          if precheck > 0 then
            let satisfiable ← chargeSearch budget <| finiteModelExists prepared.problem precheck
            if satisfiable then
              throwError "Vampire did not produce a refutation (SZS status Satisfiable); continuing with native HO"
          let firstOrder := min (← budget.get) (total * 25 / 100)
          if firstOrder < 100 then throwError "Vampire proof-search budget exhausted"
          let (parsed, strategy) ← chargeSearch budget <|
            invokeVampireStrategy prepared.problem none (some firstOrder)
          return FactReporting.markStrategy strategy (← prepared.replay parsed)
      catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        saved.restore
        let prepared ← match background? with
          | none => prepareHO
          | some (_, task) =>
            while !(← IO.hasFinished task) do
              Core.checkInterrupted
              IO.sleep 10
            match task.get with
            | .error error => throw error
            | .ok (prepared, coreState, metaState) =>
              modifyThe Core.State (fun _ => coreState)
              set metaState
              pure prepared
        withOptions hoOptions do
          let remaining ← budget.get
          if remaining < 100 then throwError "Vampire proof-search budget exhausted"
          let (parsed, strategy) ← chargeSearch budget <|
            invokeVampireStrategy prepared.problem none (some remaining)
          return FactReporting.markStrategy strategy (← prepared.replay parsed)
    )
  finally
    if let some (cancel, _) := background? then cancel

private def routeOptions (route : Routing.Route) (options : Options) : Options :=
  match route with
  | .higherOrder => options.set `vampire.higherOrder true
  | .firstOrder => options.set `vampire.higherOrder false |>.set `vampire.strategy ""

/-- Search one prepared representation with whatever budget remains and replay
its proof. A finite model of the FO abstraction is a cheap terminal failure. -/
private def searchPrepared (prepared : PreparedQuery) (budget : IO.Ref Nat)
    (alternateHO : Bool := false) : MetaM Expr := do
  let unlimited := vampire.timeLimit.get (← getOptions) == 0
  let remaining ← budget.get
  if !unlimited && remaining < 100 then throwError "Vampire proof-search budget exhausted"
  let precheck := vampire.satPrecheck.get (← getOptions)
  if precheck != 0 && (unlimited || precheck < remaining / 100) then
    if ← chargeSearch budget <| finiteModelExists prepared.problem precheck then
      throwError "Vampire did not produce a refutation (SZS status Satisfiable)"
  let remaining ← budget.get
  if !unlimited && remaining < 100 then throwError "Vampire proof-search budget exhausted"
  let (parsed, strategy) ← chargeSearch budget <|
    invokeVampireStrategy prepared.problem none (if unlimited then none else some remaining) alternateHO
  return FactReporting.markStrategy strategy (← prepared.replay parsed)

/-- Monomorphize once, then independently export, search and replay both
representations. Each worker gets the whole remaining search allowance. -/
private def replayParallel (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat)) : MetaM Expr := do
  let options ← getOptions
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (vampire.timeLimit.get options * 1000)
  let originalContext ← getLCtx
  let body : Auto.Reif.ReifM Expr := do
    let reifState ← get
    let total ← budget.get
    let processors := Processors.budget options
    let routes := if processors > 1 then #[Routing.Route.higherOrder, .firstOrder]
      else #[Routing.Route.firstOrder, .higherOrder]
    let actions := routes.map fun route => do
      let destination := vampire.outputPath.get options
      let allocation := match route with
        | .higherOrder => 1
        | .firstOrder => if processors > 1 then processors - 1 else 1
      withOptions (fun options => (Processors.withBudget (routeOptions route options) allocation).set `vampire.outputPath
          (if destination.isEmpty then "" else destination ++ s!".{route.name}.p")) do
        let prepared ← (preparedFromState originalContext).run' reifState
        let ownBudget ← IO.mkRef total
        searchPrepared prepared ownBudget
    liftM <| chargeSearch budget (if processors > 1 then raceMeta actions else firstSuccessfulMeta actions)
  let (proof, _) ← monomorphizeWithOptionalFacts lemmas inhs (fun state => body state)
  return proof

/-- Shared-preparation search. One source rewriting and monomorphization feeds
both representations: the first route is prepared and given the whole budget;
if it fails (export, search without a refutation, decoding, replay) the other
representation is prepared from the same monomorphized state and searches the
unspent remainder. Each prepared query retains its own valuation, local
context and replay closure. -/
private def replayRouted (lemmas inhs : Array Auto.Lemma) (sourceRoute : Routing.Route)
    (override? : Option Routing.Route) (budget : IO.Ref Nat) (windowed : Bool) : MetaM Expr := do
  let options ← getOptions
  let unlimited := vampire.timeLimit.get options == 0
  let destination := vampire.outputPath.get options
  let originalContext ← getLCtx
  let body : Auto.Reif.ReifM Expr := do
    let reifSaved ← get
    let metaSaved ← liftM (show MetaM Meta.SavedState from saveState)
    -- Second feature pass: the monomorphized facts are concrete, so function
    -- domains are closed and specialization-created structure is visible.
    let (chosen, features, viable) ← liftM <| Routing.choose reifSaved.facts
    let first := override?.getD chosen
    liftM <| Export.diagnosticEvent "route_selected" [
      ("stage", toJson "monomorphized"), ("route", toJson first.name),
      ("structural_route", toJson chosen.name), ("source_route", toJson sourceRoute.name),
      ("ho_viable", toJson viable), ("features", features.toJson)]
    let attempt (route : Routing.Route) (restore : Bool) : Auto.Reif.ReifM Expr := do
      if restore then
        liftM metaSaved.restore
        set reifSaved
      let prepared ← withOptions (routeOptions route) (preparedFromState originalContext)
      liftM <| withOptions (routeOptions route) <| searchPrepared prepared budget
    try
      attempt first false
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      if ← liftM (deferredRecoveryApplies error) then throw error
      let message ← liftM error.toMessageData.toString
      let remaining ← (budget.get : BaseIO Nat)
      if !unlimited && remaining < 1000 then throw error
      liftM <| Export.diagnosticEvent "route_switched" [
        ("from", toJson first.name), ("to", toJson first.other.name),
        ("remaining_ms", toJson remaining), ("error", toJson message)]
      unless destination.isEmpty do
        liftM <| show MetaM Unit from do
          for suffix in ["", ".stdout", ".stderr", ".exitcode", ".fmb.stdout"] do
            let source : System.FilePath := destination ++ suffix
            if ← source.pathExists then
              IO.FS.rename source (destination ++ s!".{first.name}-first" ++ suffix)
      attempt first.other true
  let continuation (state : Auto.Reif.State) : MetaM (Expr × Auto.Reif.State) := body state
  let (proof, _) ← if windowed then
    withMonoDeadline fun resume => monomorphizeWithOptionalFacts lemmas inhs (resume ∘ continuation)
  else
    monomorphizeWithOptionalFacts lemmas inhs continuation
  return proof

/-- Time-sliced HO -> FO -> HO search over one shared monomorphization. The
first native slice gets `vampire.sliceHoFirst` percent of the budget; FO gets
`vampire.sliceFo` percent plus whatever the first slice left unspent. The final
HO slice, with the alternate native strategy and all remaining time, runs only
if FO ended before its slice was used up (a finite model of the abstraction,
`GaveUp`, or another early failure), not when FO timed out, and only if the
HO query was prepared. When the native slice fails on a missing domain that the
tactic's deferred-inhabitant recovery repairs, FO first searches the unchanged
goal for `vampire.sliceFoBeforeRecovery` percent, then the error is rethrown so
the recovery can retry with the time left.

`monomorphizeWithOptionalFacts` treats a translation error escaping its
continuation as a sign that generated facts are untranslatable, and reruns the
monomorphization without them. A native export failure must not do that to the
first-order problem, which translates with them. The continuation therefore
returns every outcome as a value: only an error that the first-order
preparation raises is allowed to escape, so that retry stays available to
it. The slice state lives in refs, so a rerun does not search the native slice
again. -/
private def replayRoutedSlices (lemmas inhs : Array Auto.Lemma) (budget : IO.Ref Nat) :
    MetaM Expr := do
  let options ← getOptions
  if vampire.timeLimit.get options == 0 then
    throwError "vampire.routedSlices requires a finite positive timeLimit"
  let total ← budget.get
  let destination := vampire.outputPath.get options
  let originalContext ← getLCtx
  let cap1 := total * vampire.sliceHoFirst.get options / 100
  -- Refs, not `let mut`: mutations made before a throw are lost to `catch`, and
  -- a monomorphization rerun must see what the first pass already did.
  let hoAttempted ← IO.mkRef false
  let hoPrepared ← IO.mkRef (none : Option PreparedQuery)
  let hoState ← IO.mkRef (none : Option Meta.SavedState)
  let pendingRef ← IO.mkRef (none : Option Exception)
  let spent1 ← IO.mkRef 0
  let slice (prepared : PreparedQuery) (cap : Nat) (alternate : Bool) : MetaM Expr := do
    let before ← budget.get
    let allotted := min cap before
    let sub ← IO.mkRef allotted
    try
      searchPrepared prepared sub alternate
    finally
      budget.modify (· - (allotted - min allotted (← sub.get)))
  let archive (suffix : String) : MetaM Unit := do
    unless destination.isEmpty do
      for extension in ["", ".stdout", ".stderr", ".exitcode", ".fmb.stdout"] do
        let source : System.FilePath := destination ++ extension
        if ← source.pathExists then
          IO.FS.rename source (destination ++ suffix ++ extension)
  let body : Auto.Reif.ReifM (Except Exception Expr) := do
    let reifSaved ← get
    let metaSaved ← liftM (show MetaM Meta.SavedState from saveState)
    -- Slice 1: native higher-order, once.
    if cap1 > 0 && !(← hoAttempted.get) then
      hoAttempted.set true
      let hoAttempt : Auto.Reif.ReifM Expr := do
        let prepared ← withOptions (routeOptions .higherOrder) (preparedFromState originalContext)
        hoPrepared.set (some prepared)
        hoState.set (some (← liftM (show MetaM Meta.SavedState from saveState)))
        let before ← liftM (budget.get : BaseIO Nat)
        try
          liftM <| withOptions (routeOptions .higherOrder) <| slice prepared cap1 false
        finally
          spent1.set (before - (← liftM (budget.get : BaseIO Nat)))
      try
        return .ok (← hoAttempt)
      catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        let mut cause := error
        let first ← liftM error.toMessageData.toString
        if isUnsupportedTranslation first && (← hoPrepared.get).isNone then
          -- The optional facts may be what the native export cannot translate.
          -- Retry for this route alone, from the state saved at entry, so the
          -- first-order route keeps them.
          liftM <| Export.diagnosticEvent "monomorphization_retry" [
            ("route", toJson "ho"), ("omitting", toJson "generated facts"),
            ("error", toJson (first.take 300))]
          liftM metaSaved.restore
          set reifSaved
          try
            let (proof, _) ← liftM (monomorphizeWithoutGeneratedFacts lemmas inhs
              (fun state => hoAttempt state))
            return .ok proof
          catch retryError =>
            if retryError.isInterrupt || retryError.isRuntime then throw retryError
            cause := retryError
        if ← liftM (deferredRecoveryApplies cause) then pendingRef.set (some cause)
        let message ← liftM cause.toMessageData.toString
        liftM <| Export.diagnosticEvent "slice_failed" [("slice", toJson "ho"), ("error", toJson message)]
        liftM <| archive ".ho-first"
        liftM metaSaved.restore
        set reifSaved
    -- Slice 2: first-order. A preparation error escapes on purpose.
    let remaining ← liftM (budget.get : BaseIO Nat)
    let pending ← pendingRef.get
    let unspent := cap1 - min cap1 (← spent1.get)
    let cap2 := if pending.isSome then
      min remaining (total * vampire.sliceFoBeforeRecovery.get options / 100)
    else min remaining (total * vampire.sliceFo.get options / 100 + unspent)
    let prepared ← withOptions (routeOptions .firstOrder) (preparedFromState originalContext)
    let mut failure : Exception := Exception.error .missing m!"sliced search failed"
    let mut earlyFo := false
    try
      return .ok (← liftM <| withOptions (routeOptions .firstOrder) <| slice prepared cap2 false)
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      if ← liftM (deferredRecoveryApplies error) then return .error error
      failure := error
      let message ← liftM error.toMessageData.toString
      earlyFo := !message.startsWith "Vampire timed out"
      liftM <| Export.diagnosticEvent "slice_failed" [
        ("slice", toJson "fo"), ("early", toJson earlyFo), ("error", toJson message)]
    -- Slice 3: native higher-order again, with the alternate strategy.
    let remaining ← liftM (budget.get : BaseIO Nat)
    if earlyFo && remaining >= 100 then
      if let (some prepared, some state) := (← hoPrepared.get, ← hoState.get) then
        liftM <| archive ".fo-second"
        liftM state.restore
        try
          return .ok (← liftM <| withOptions (routeOptions .higherOrder) <| slice prepared remaining true)
        catch error =>
          if error.isInterrupt || error.isRuntime then throw error
          return .error error
    -- The first-order slice failed on the unchanged goal: let the tactic repair
    -- the missing domain and search natively with the remaining time.
    if let some domainError := pending then
      if remaining >= 100 then return .error domainError
    return .error failure
  let (result, _) ← monomorphizeWithOptionalFacts lemmas inhs (fun state => body state)
  match result with
  | .ok proof => return proof
  | .error error => throw error

/-- Choose the first representation from cheap structural features and run
`replayRouted`. A blown first-order monomorphization window retries natively
higher-order without saturation, as in `replayWithMonoFallback`. -/
private def replayRoutedSearch (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat)) : MetaM Expr := do
  let options ← getOptions
  let limit := vampire.timeLimit.get options
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (limit * 1000)
  if vampire.routedSlices.get options then return ← replayRoutedSlices lemmas inhs budget
  let (chosen, features, viable) ← Routing.choose (lemmas.map (·.toUMonoFact))
  let override? := match InternalSearch.routeOverride options with
    | "fo" => some Routing.Route.firstOrder
    | "ho" => some .higherOrder
    | _ => none
  let first := override?.getD chosen
  Export.diagnosticEvent "route_selected" [
    ("stage", toJson "source"), ("route", toJson first.name),
    ("structural_route", toJson chosen.name),
    ("override", toJson (InternalSearch.routeOverride options)),
    ("ho_viable", toJson viable), ("features", features.toJson)]
  let windowed := first == .firstOrder && vampire.monoHeartbeats.get options > 0
  let saved ← saveState
  try
    withOptions (routeOptions first) <| replayRouted lemmas inhs first override? budget windowed
  catch error =>
    let message ← error.toMessageData.toString
    unless windowed && isMonoDeadline message && (limit == 0 || (← budget.get) >= 1000) do throw error
    saved.restore
    withOptions (fun options => (routeOptions .higherOrder options).set `auto.mono.saturationThreshold 0) <|
      replayRouted lemmas inhs .higherOrder (some .higherOrder) budget false

/-- Native higher-order search and its first-order retry use independent
translation states and one total search budget. Export-only calls retain the
explicitly requested representation. -/
def replayVampireWithAuto (lemmas inhs : Array Auto.Lemma)
    (searchBudget? : Option (IO.Ref Nat) := none)
    (deferMonoFallback : Bool := false) (monoBudget? : Option (IO.Ref Nat) := none) : MetaM Expr := do
  let options ← getOptions
  if vampire.parallel.get options then
    return ← replayParallel lemmas inhs searchBudget?
  if vampire.routedSlices.get options then
    return ← replayRoutedSearch lemmas inhs searchBudget?
  if InternalSearch.staged options then
    return ← replayStaged lemmas inhs searchBudget?
  if InternalSearch.routed options then
    return ← replayRoutedSearch lemmas inhs searchBudget?
  unless vampire.higherOrder.get options && vampire.higherOrderFallback.get options do
    if !vampire.higherOrder.get options && vampire.monoHeartbeats.get options > 0 then
      return ← replayWithMonoFallback lemmas inhs searchBudget? deferMonoFallback monoBudget?
    return ← replayWithRecordLawRetry lemmas inhs searchBudget? monoBudget?
  let limit := vampire.timeLimit.get options
  let unlimited := limit == 0
  let budget ← match searchBudget? with
    | some budget => pure budget
    | none => IO.mkRef (limit * 1000)
  let total ← budget.get
  let allotted := min total (max 1000 (total * min 100 (vampire.higherOrderSliceShare.get options) / 100))
  let nativeBudget ← if unlimited then pure budget else IO.mkRef allotted
  let saved ← saveState
  try
    try
      replayWithRecordLawRetry lemmas inhs (some nativeBudget)
    finally
      unless unlimited do
        budget.modify (· - (allotted - min allotted (← nativeBudget.get)))
  catch error =>
    if ← deferredRecoveryApplies error then throw error
    let message ← error.toMessageData.toString
    unless canRetryFirstOrder message && (unlimited || (← budget.get) >= 1000) do throw error
    saved.restore
    let destination := vampire.outputPath.get options
    -- An export failure has not written this attempt's input or output.
    unless destination.isEmpty || message.startsWith "THF export:" do
      for suffix in ["", ".stdout", ".stderr", ".exitcode", ".fmb.stdout"] do
        let source : System.FilePath := destination ++ suffix
        if ← source.pathExists then
          IO.FS.rename source (destination ++ ".higher-order" ++ suffix)
    trace[vampire] "Retrying native higher-order failure with first-order encoding: {message}"
    -- Encoded higher-order strategies are unsuitable for the first-order
    -- portfolio; its normal strategy selection applies to the retry.
    withOptions (fun options => options.set `vampire.higherOrder false |>.set `vampire.strategy ""
      |>.set `vampire.monoHeartbeats 0) <|
      replayWithRecordLawRetry lemmas inhs (some budget)
end VampireHammer.Export.Internal

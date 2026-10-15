import VampireHammer.Export.SiblingLemmas
import Lean.LibrarySuggestions.Default

/-!
# Library-suggestion premises

The attribute and sibling collectors only reach theorems that are indexed by
`simp`/`grind` or whose statements match a source proposition up to
definitional unfolding. Many facts a first-order proof needs share symbols with
the goal without matching any of its propositions: `covariance_const_mul_right`
for a goal about `covariance X (fun ω => Y ω * c)`, say.

This collector asks Lean core's library-suggestion engine (`Lean.LibrarySuggestions`,
by default the Sine Qua Non relevance filter of Hoder and Voronkov over all
imported theorems) for theorems relevant to the refutation goal. The engine
uses only the symbols of the goal and its local hypotheses, so the collector
contains no mathematical theory. Each accepted suggestion is the original
polymorphic theorem; lean-auto's monomorphization instantiates it against the
terms of the problem, and the reconstructed proof uses the theorem itself.

Selected facts are automatic premises: an untranslatable one is omitted
individually, exactly like an attribute lemma. Suggestions proved from the
target theorem, or introducing datatypes absent from the source problem, are
refused. Collection runs in its own heartbeat window like sibling selection,
so a slow selector discards only the suggestions.
-/

open Lean Meta

register_option vampire.suggestedLemmas : Nat := {
  defValue := 0
  descr := "Maximum theorems taken from Lean's library-suggestion engine (0 disables)"
}

namespace VampireHammer.SuggestedLemmas

def labelPrefix := "suggested lemma "

/-- Heartbeat window for one collection, in the units of `IO.getNumHeartbeats`. -/
private def collectionBudget : Nat := 20_000_000

/-- Skip selection when the enclosing command has less than this budget left. -/
private def headroomFloor : Nat := 40_000_000

/-- Module indices that are the target's module or import it transitively.
Only declarations in these modules can depend on the target. Module indices
are topologically ordered, so one forward pass suffices. -/
private def downstreamModules (env : Environment) (target : Name) : Std.HashSet Nat := Id.run do
  let some origin := env.getModuleIdxFor? target | return {}
  let mut downstream : Std.HashSet Nat := {}
  let mut indices : Std.HashMap Name Nat := {}
  for (name, index) in env.header.moduleNames.zipIdx do
    indices := indices.insert name index
  downstream := downstream.insert origin.toNat
  for (data, index) in env.header.moduleData.zipIdx do
    if index <= origin.toNat then continue
    if data.imports.any fun i => (indices[i.module]?.map downstream.contains).getD false then
      downstream := downstream.insert index
  return downstream

/-- Whether `proof` transitively uses `target`. A dependency path to the
target only passes through declarations of `downstream` modules, so the walk
does not leave them. -/
private def dependsOn (env : Environment) (downstream : Std.HashSet Nat) (target : Name)
    (proof : Expr) : Bool := Id.run do
  let mut pending := proof.getUsedConstants
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    if name == target then return true
    let some module := env.getModuleIdxFor? name | continue
    unless downstream.contains module.toNat do continue
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  return false

private def collectCore (lemmas : Array Auto.Lemma) (target : Expr) (exclude? : Option Name)
    (limit : Nat) : MetaM (Array Auto.Lemma) := do
  let mut knownDomains : Std.HashSet Name := {}
  for lemma in lemmas do
    for name in (← AttributeLemmas.domainHeads lemma.type).toArray do
      knownDomains := knownDomains.insert name
  let goal ← mkFreshExprMVar target
  -- Ask for more than the limit: domain and dependency filters reject some.
  let suggestions ← Lean.LibrarySuggestions.select goal.mvarId!
    { maxSuggestions := 2 * limit, caller := some "vampire",
      filter := fun name => return exclude? != some name }
  let env ← getEnv
  let downstream := match exclude? with
    | some target => downstreamModules env target
    | none => {}
  let origin? := exclude?.bind env.getModuleIdxFor?
  let mut result := #[]
  for suggestion in suggestions do
    if result.size >= limit then break
    checkSystem "suggested lemma collection"
    let name := suggestion.name
    let some (.thmInfo _) := (← getEnv).find? name | continue
    let lemma? ← SiblingLemmas.attempt 2_000_000 do
      let lemma ← Auto.Lemma.ofConst name (.leaf s!"{labelPrefix}{name}")
      Auto.unfoldConstAndPreprocessLemma #[] lemma
    let some lemma := lemma? | continue
    -- Theorems of modules importing the target's module are refused, so only
    -- premises available before the target are used. A declaration of the
    -- target's own module is refused when it depends on the target.
    if let some module := env.getModuleIdxFor? name then
      if downstream.contains module.toNat then
        if origin? != some module then continue
        if let some target := exclude? then
          if dependsOn env downstream target lemma.proof then
            trace[vampire.premises] "Rejected suggestion {name}: depends on {target}"
            continue
    let heads? ← SiblingLemmas.attempt 2_000_000 <| AttributeLemmas.domainHeads lemma.type
    let some heads := heads? | continue
    unless heads.toArray.all knownDomains.contains do
      trace[vampire.premises] "Rejected suggestion {name}: new datatypes {heads.toArray}"
      continue
    unless lemmas.any (·.type == lemma.type) do
      trace[vampire.premises] "Selected suggestion {name} (score {suggestion.score})"
      result := result.push lemma
  return result

/-- Select up to `vampire.suggestedLemmas` theorems relevant to `target` in the
current local context. `lemmas` are the requested facts; their datatypes bound
the datatypes a suggestion may introduce. -/
def collect (lemmas : Array Auto.Lemma) (target : Expr) (exclude? : Option Name := none) :
    MetaM (Array Auto.Lemma) := do
  let limit := vampire.suggestedLemmas.get (← getOptions)
  if limit == 0 then return #[]
  let coreCtx ← readThe Core.Context
  let entry ← IO.getNumHeartbeats
  let remaining := coreCtx.maxHeartbeats - (entry - coreCtx.initHeartbeats)
  if coreCtx.maxHeartbeats != 0 && remaining < headroomFloor then
    trace[vampire.premises] "suggestion selection skipped: {remaining} heartbeats left"
    return #[]
  let budget :=
    if coreCtx.maxHeartbeats == 0 then collectionBudget
    else min collectionBudget (remaining / 4)
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      let result ← SiblingLemmas.withHeartbeatBudget budget <|
        collectCore lemmas target exclude? limit
      return result)
    (fun error => do
      saved.restore
      SiblingLemmas.checkOptionalFailure error
      trace[vampire.premises] "suggestion selection aborted: {error.toMessageData}"
      return #[])

end VampireHammer.SuggestedLemmas

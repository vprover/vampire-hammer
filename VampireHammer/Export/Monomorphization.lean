import VampireHammer.Export.Premises
import VampireHammer.Export.DefinitionAlignment
import VampireHammer.Export.CoercionNormalization
import VampireHammer.Export.Diagnostics

/-! Keep automatically selected premises from blocking translation of the
requested problem. Retrying with fewer premises weakens a refutation problem;
the reconstructed proof is still checked against the original Lean goal. -/

namespace VampireHammer.Export.Internal

open Lean Meta

/-- Resolve the temporary definitions introduced by monomorphization before
its local context disappears. Atom valuations may mention these definitions
inside types, instances or proof arguments, even after their outer symbol has
been resolved. Preserve the caller's own variables and lets. -/
def closeMonomorphizationProof (original : LocalContext) (proof : Expr) : MetaM Expr := do
  let used := (collectFVars {} proof).fvarIds
  if used.all original.contains then return proof
  let temporary := (← getLCtx).getFVarIds.filter fun id => !original.contains id
  let proof ← zetaDeltaFVars proof temporary
  for id in (collectFVars {} proof).fvarIds do
    unless original.contains id do
      throwError "Vampire replay retained an unbound temporary variable `{id.name}`"
  return proof

partial def isAutomaticSource : Auto.DTr → Bool
  | .leaf label => label.startsWith typeclassLawLabel || label.startsWith structureLawLabel ||
      label.startsWith AttributeLemmas.labelPrefix ||
      label.startsWith ConstructorFacts.labelPrefix ||
      label.startsWith InstanceDefinitions.labelPrefix ||
      label.startsWith ProjectionDefinitions.labelPrefix ||
      label.startsWith CoercionBridges.labelPrefix ||
      label.startsWith SiblingLemmas.labelPrefix ||
      label.startsWith SuggestedLemmas.labelPrefix ||
      label.startsWith DefinitionAlignment.labelPrefix ||
      label.startsWith DataWitnesses.labelPrefix ||
      label.startsWith CoercionNormalization.labelPrefix ||
      label.startsWith CoercionNormalization.lawLabelPrefix ||
      label.startsWith DefinitionAlignment.inverseLabelPrefix
  | .node _ premises => !premises.isEmpty && premises.all isAutomaticSource

def isUnsupportedTranslation (message : String) : Bool :=
  message.contains "Auto.Monomorphization." ||
  message.contains "Monomorphization failed because" ||
  message.contains "Auto.LamReif." || message.contains "Auto.Reif.resolveTy" ||
  message.startsWith "TFF export:" || message.startsWith "THF export:"

/-- Whether any fact of the derivation tree carries the given label prefix. -/
private partial def mentionsLabelPrefix (wanted : String) : Auto.DTr → Bool
  | .leaf label => label.startsWith wanted
  | .node _ premises => premises.any (mentionsLabelPrefix wanted)

/-- Label prefix lean-auto gives explicit hint terms (`❰term❱`). -/
private def hintLabelPrefix : String := "❰"

/-- One monomorphization of `facts`, then the export/replay continuation. -/
private def runMonomorphization (facts inhs : Array Auto.Lemma)
    (continuation : Auto.Reif.State → MetaM α)
    (extend : Array Auto.Lemma → MetaM (Array Auto.Lemma)) (omitHints : Bool)
    (omitLocals : Bool := false) : MetaM α := do
  let facts ← SourceNormalization.prepareForMonomorphization facts
  -- The `ciInstDefEq` facts are generated inside monomorphization from the
  -- const instances of the collected facts; they are not requested by the
  -- user. An untranslatable one is omitted like any other automatic fact
  -- instead of aborting the requested problem.
  let prefixes := String.intercalate ";"
    ([typeclassLawLabel, structureLawLabel, AttributeLemmas.labelPrefix,
     ConstructorFacts.labelPrefix, InstanceDefinitions.labelPrefix,
     ProjectionDefinitions.labelPrefix, CoercionBridges.labelPrefix,
     SiblingLemmas.labelPrefix,
     SuggestedLemmas.labelPrefix, DefinitionAlignment.labelPrefix, DataWitnesses.labelPrefix,
     DefinitionAlignment.inverseLabelPrefix, CoercionNormalization.labelPrefix,
     CoercionNormalization.lawLabelPrefix, "ciInstDefEq"] ++ (if omitHints then [hintLabelPrefix] else []) ++
     (if omitLocals then ["lctxLem"] else []))
  -- Discovered sibling facts add polymorphic constants whose instantiations
  -- consume saturation matches. The fixed threshold would then truncate
  -- saturation early and silently evict the requested problem's own facts
  -- from the exported problem. Scale the budget for the discovered facts only.
  let threshold := auto.mono.saturationThreshold.get (← getOptions)
  let discovered fact := mentionsLabelPrefix SiblingLemmas.labelPrefix fact.deriv ||
    mentionsLabelPrefix SuggestedLemmas.labelPrefix fact.deriv
  let scaled := if facts.any discovered then
    4 * threshold else threshold
  withOptions (fun options => options.set
      `auto.mono.ignoreUnsupportedFactPrefixes prefixes |>.set
      `auto.mono.saturationThreshold scaled) do
    -- Definitions are aligned on the instantiated facts; see `DefinitionAlignment`.
    Auto.Monomorphization.monomorphize facts inhs (fun state => do
      -- lean-auto's representation context retains variables opened while
      -- inspecting quantified facts. Its instance search can mistake one of
      -- those binders for a domain witness. Only witnesses closed over the
      -- actual continuation context may reach reification.
      let context ← getLCtx
      let inhTys ← state.inhTys.filterM fun fact => do
        let proof ← instantiateMVars fact.proof
        pure ((collectFVars {} proof).fvarIds.all context.contains)
      let facts := state.facts.map fun fact =>
        if mentionsLabelPrefix "ciInstDefEq" fact.deriv then
          let proof := mkApp3 (mkConst ``FactReporting.additionalFact) fact.type
            (toExpr (toString fact.deriv)) fact.proof
          { fact with proof }
        else fact
      continuation { state with inhTys, facts }) extend

/-- Recover from an unsupported translation of `lemmas`: retry with
untranslatable instances of explicit hints omitted as well (a premise list
taken from a library proof often contains a lemma that lean-auto cannot
monomorphize, and omitting a fact from a refutation problem is sound), then
once using all local hypotheses and explicit hints, without automatic class
laws or attribute lemmas. The first attempt keeps explicit hints required, so
an unusable hint of an interactive call is still reported. If enabled, a final
monomorphization retry also omits unrepresentable local hypothesis instances;
the negated goal remains required. Search, parser, replay and resource-limit
failures are propagated. -/
private def recoverMonomorphization (lemmas inhs : Array Auto.Lemma)
    (continuation : Auto.Reif.State → MetaM α)
    (extend : Array Auto.Lemma → MetaM (Array Auto.Lemma)) (saved : SavedState)
    (error : Exception) : MetaM α := do
  let required := lemmas.filter fun lemma => !isAutomaticSource lemma.deriv
  let hinted := lemmas.any fun lemma => mentionsLabelPrefix hintLabelPrefix lemma.deriv
  let supportedSubset (error : Exception) : MetaM α := do
    unless vampire.omitUnsupportedLocalHypotheses.get (← getOptions) do throw error
    let message ← error.toMessageData.toString
    unless message.contains "Monomorphization" do throw error
    saved.restore
    trace[vampire] "Retrying monomorphization with only representable local hypothesis instances: {message}"
    Export.diagnosticEvent "monomorphization_retry" [("omitting", toJson "unsupported local hypotheses"), ("error", toJson (message.take 300))]
    -- Omitting a hypothesis weakens the refutation problem; every retained
    -- premise still carries its original checked Lean proof. This cannot
    -- manufacture inhabitants or translate an essential dependent premise.
    try
      runMonomorphization lemmas inhs continuation extend true true
    catch retryError =>
      if retryError.isInterrupt || retryError.isRuntime then throw retryError
      if isUnsupportedTranslation (← retryError.toMessageData.toString) then throw error
      throw retryError
  let withoutAutomatic (error : Exception) : MetaM α := do
    unless required.size < lemmas.size &&
        isUnsupportedTranslation (← error.toMessageData.toString) do return ← supportedSubset error
    saved.restore
    trace[vampire] "Retrying unsupported translation without {lemmas.size - required.size} automatic premises: {error.toMessageData}"
    Export.diagnosticEvent "monomorphization_retry" [("omitting", toJson "automatic premises"), ("dropped", toJson (lemmas.size - required.size)), ("error", toJson ((← error.toMessageData.toString).take 300))]
    try runMonomorphization required inhs continuation extend hinted
    catch retryError => supportedSubset retryError
  -- Only monomorphization omits facts; an export failure is not affected.
  let message ← error.toMessageData.toString
  unless hinted && message.contains "Monomorphization" do return ← withoutAutomatic error
  saved.restore
  trace[vampire] "Retrying unsupported translation without untranslatable hint instances: {message}"
  Export.diagnosticEvent "monomorphization_retry" [("omitting", toJson "untranslatable hint instances"), ("error", toJson (message.take 300))]
  try runMonomorphization lemmas inhs continuation extend true
  catch error => withoutAutomatic error

private def isGenerated (lemma : Auto.Lemma) : Bool :=
  mentionsLabelPrefix DataWitnesses.labelPrefix lemma.deriv

/-- Translate the complete problem. Facts generated for it, by `DataWitnesses`
before and by `DefinitionAlignment` during monomorphization, are dropped
first if the translation is unsupported: they must never lose a problem that
translates without them. Then `recoverMonomorphization` applies. All attempts
share the same export/replay continuation. -/
def monomorphizeWithOptionalFacts (lemmas inhs : Array Auto.Lemma)
    (continuation : Auto.Reif.State → MetaM α) : MetaM α := do
  let extended ← IO.mkRef false
  let extend facts := do
    if vampire.onlyFacts.get (← getOptions) then return #[]
    let added := (← DefinitionAlignment.extend facts) ++ (← CoercionNormalization.extend facts)
    let added := added.map FactReporting.markLemma
    let added ← SourceNormalization.prepareForMonomorphization added
    unless added.isEmpty do extended.set true
    return added
  let saved ← saveState
  try
    runMonomorphization lemmas inhs continuation extend false
  catch error =>
    let plain := lemmas.filter (!isGenerated ·)
    unless isUnsupportedTranslation (← error.toMessageData.toString) &&
        (plain.size < lemmas.size || (← extended.get)) do
      return ← recoverMonomorphization lemmas inhs continuation extend saved error
    saved.restore
    trace[vampire] "Retrying unsupported translation without generated facts: {error.toMessageData}"
    Export.diagnosticEvent "monomorphization_retry" [("omitting", toJson "generated facts"), ("error", toJson ((← error.toMessageData.toString).take 300))]
    let none : Array Auto.Lemma → MetaM (Array Auto.Lemma) := fun _ => pure #[]
    try runMonomorphization plain inhs continuation none false
    catch error => recoverMonomorphization plain inhs continuation none saved error

/-- One monomorphization without the facts generated for the problem
(`DataWitnesses`, definition alignment, coercion normalization), with no further
recovery. The retry `monomorphizeWithOptionalFacts` applies after an
unsupported translation, available to a single route of a shared preparation
so that its failure does not change the facts of the other route. -/
def monomorphizeWithoutGeneratedFacts (lemmas inhs : Array Auto.Lemma)
    (continuation : Auto.Reif.State → MetaM α) : MetaM α := do
  let none : Array Auto.Lemma → MetaM (Array Auto.Lemma) := fun _ => pure #[]
  runMonomorphization (lemmas.filter (!isGenerated ·)) inhs continuation none false

end VampireHammer.Export.Internal

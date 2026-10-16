import Auto.Tactic
import VampireHammer.TFF
import VampireHammer.THF
import VampireHammer.Export.Monomorphization
import VampireHammer.Export.Inhabitation
import VampireHammer.Export.FirstOrderEncoding
import VampireHammer.Export.LawInstances
import VampireHammer.Export.Diagnostics
import VampireHammer.Export.Reification

/-!
TF0 export inside the live reification context and filtering of unsupported automatically
collected laws.
-/

namespace VampireHammer.Export.Internal

open Lean Meta Elab Tactic

/-- Preserve goal provenance through transformations of the negated goal alone.
An arbitrary negative hypothesis, or a consequence mixing goal and premises,
must not be identified as the original conjecture. -/
private partial def derivesOnlyFromNegatedGoal : Auto.DTr → Bool
  | .leaf label => label == negatedGoalLabel
  | .node _ premises => !premises.isEmpty && premises.all derivesOnlyFromNegatedGoal

/-- Convert already reified and preprocessed first-order facts to the project
TF0 representation. Keeping this inside `LamReif.ReifM` preserves the precise
lean-auto atom valuation needed by replay. -/
def exportPreprocessedFacts (facts : Array Auto.Embedding.Lam.REntry) :
    Auto.LamReif.ReifM TFF.Problem := do
  let terms ← facts.mapM fun fact => do
    match fact with
    | .valid [] term => pure term
    | _ => throwError "Unexpected non-formula export entry"
  let varTys := (← Auto.LamReif.getVarVal).map Prod.snd
  let evarTys ← Auto.LamReif.getLamEVarTy
  let nonemptySorts := (← Auto.LamReif.getRst).nonemptyMap.toArray.map Prod.fst
  let negatedConjectures ← facts.mapM fun fact =>
    derivesOnlyFromNegatedGoal <$> Auto.LamReif.collectDerivFor fact
  let exported := if vampire.higherOrder.get (← getOptions) then
    THF.exportProblem varTys evarTys nonemptySorts terms negatedConjectures
  else TFF.exportProblem varTys evarTys nonemptySorts terms negatedConjectures
  match exported with
  | .ok problem => pure problem
  | .error message =>
    -- Name the Lean type of an uninhabited sort; `s_aN` alone is opaque.
    let index? := (message.splitOn "sort s_a")[1]? >>= fun rest =>
      (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat?
    let some index := index? | do
      if message.contains "sort Empty has no known inhabitation evidence" then
        throwError (← Export.missingDomainMessage message (mkConst ``Empty))
      throwError "{message}"
    let some (type, _) := (← Auto.LamReif.getTyVal)[index]? | throwError "{message}"
    throwError (← Export.missingDomainMessage message type)

/-- Whether every source assertion is an optional generated or selected fact. -/
private partial def derivesOnlyFromAuxiliaryFacts : Auto.DTr → Bool
  | .leaf label => label.startsWith typeclassLawLabel || label.startsWith structureLawLabel ||
      label.startsWith AttributeLemmas.labelPrefix ||
      label.startsWith "first-order encoding " ||
      label.startsWith ConstructorFacts.labelPrefix ||
      label.startsWith InstanceDefinitions.labelPrefix ||
      label.startsWith ProjectionDefinitions.labelPrefix ||
      label.startsWith CoercionBridges.labelPrefix ||
      label.startsWith LawInstances.labelPrefix ||
      label.startsWith SiblingLemmas.labelPrefix ||
      label.startsWith SuggestedLemmas.labelPrefix
  | .node _ premises => !premises.isEmpty && premises.all derivesOnlyFromAuxiliaryFacts

/-- Drop preprocessed facts that lie outside the TF0 fragment, but only when
they stem exclusively from automatically collected laws, indexed lemmas or
checked object-encoding definitions.

A local instance such as `[Group G]` contributes *every* proposition-valued
field, including laws that quantify over unsupported higher-order domains.
The user did not ask for these, and omitting an axiom from a refutation problem
is sound, so they are discarded with a trace message. Unsupported local
hypotheses and explicit hints remain for `exportPreprocessedFacts` to report. -/
def dropUnsupportedTypeclassLaws (facts : Array Auto.Embedding.Lam.REntry) :
    Auto.LamReif.ReifM (Array Auto.Embedding.Lam.REntry) := do
  let varTys := (← Auto.LamReif.getVarVal).map Prod.snd
  let evarTys ← Auto.LamReif.getLamEVarTy
  let nonemptySorts := (← Auto.LamReif.getRst).nonemptyMap.toArray.map Prod.fst
  facts.filterM fun fact => do
    let .valid _ term := fact | pure true
    let checker := if vampire.higherOrder.get (← getOptions) then THF.checkFact else TFF.checkFact
    let .error message := checker varTys evarTys nonemptySorts term | pure true
    let deriv ← Auto.LamReif.collectDerivFor fact
    if derivesOnlyFromAuxiliaryFacts deriv then
      trace[vampire] "Dropping auxiliary fact outside the TF0 fragment ({message}): {deriv}"
      pure false
    else
      pure true

/-- Whether `term` quantifies over `Prop`. -/
private partial def quantifiesProp : Auto.Embedding.Lam.LamTerm → Bool
  | .base (.forallE (.base .prop)) | .base (.existE (.base .prop)) => true
  | .app _ fn arg => quantifiesProp fn || quantifiesProp arg
  | .lam _ body => quantifiesProp body
  | _ => false

/-- Try the established first-order path first. The object encoding is only
used for unsupported function/proposition values, before any prover process
is started. Both reification states and Lean's metavariable state are restored
before retrying, so a failed translation cannot leave stale symbols behind. -/
def prepareFirstOrderProblem (sources inhs : Array Auto.UMonoFact)
    (inductives : Array (Array Auto.SimpleIndVal)) :
    Auto.LamReif.ReifM (TFF.Problem × Array Auto.Embedding.Lam.REntry) := do
  let savedLam ← get
  let savedReif ← liftM (show Auto.Reif.ReifM Auto.Reif.State from get)
  let savedMeta ← liftM (show MetaM Meta.SavedState from saveState)
  try
    prepare false
  catch error =>
    if vampire.higherOrder.get (← getOptions) then throw error
    unless vampire.higherOrderEncoding.get (← getOptions) do throw error
    -- The exporter marks exactly the errors that the object encoding avoids.
    let message ← error.toMessageData.toString
    unless message.contains TFF.objectEncodingSuffix do throw error
    liftM savedMeta.restore
    set savedLam
    liftM (show Auto.Reif.ReifM Unit from set savedReif)
    trace[vampire] "Retrying TF0 translation with checked function/proposition object encoding"
    prepare true
where
  prepare (encode : Bool) := do
    let _ ← Auto.LamReif.reifInhabitations inhs
    let facts ← if encode then FirstOrderEncoding.encodeFacts sources else do
      let facts ← reifyCheckedFacts sources
      pure (facts.map (.valid []))
    let witnessBudget ← liftM <| Export.SearchAllowance.create (vampire.domainWitnessHeartbeats.get (← getOptions))
    deriveDomainInhabitants (some witnessBudget)
    let facts ← dropUnsupportedTypeclassLaws facts
    -- The ordinary path keeps Auto's full inductive theory. The fallback adds
    -- checked structure projections at source constructor applications.
    let inds ← if encode then pure #[] else Auto.LamReif.reifMutInds inductives
    let (facts, _) ← Auto.LamReif.preprocess facts inds
    -- lean-auto's checked meaning of the `Bool` constants and of `ite` at each
    -- sort, which both exporters keep as uninterpreted symbols.
    -- `ofProp`'s specification quantifies over propositions, which TF0 cannot;
    -- `ofProp` itself is exported only in THF.
    let auxiliary ← Auto.LamReif.auxLemmas facts
    let higherOrder := vampire.higherOrder.get (← getOptions)
    let facts := facts ++ auxiliary.filter fun fact =>
      higherOrder || !(fact.allLamTerms.any fun term => quantifiesProp term)
    -- Auto also introduces checked definitional equalities during
    -- monomorphization/preprocessing; filter their unsupported fragments too.
    let facts ← dropUnsupportedTypeclassLaws facts
    deriveDomainInhabitants (some witnessBudget)
    let problem ← exportPreprocessedFacts facts
    return (problem, facts)

end VampireHammer.Export.Internal

namespace VampireHammer

open Lean Meta
open Export.Internal

/-- Use lean-auto's checked preprocessing before exporting TF0.  Its current
Skolemization pass handles a leading `∀* ∃*` prefix, but does not first put an
arbitrary formula into NNF or prenex form.  Source-side formulas whose
existentials are hidden below negation should therefore be normalized with
VampLean before this boundary.  When the prefix is visible, Vampire sees
lean-auto's witness terms as ordinary input symbols. -/
def exportProblem (lemmas inhs : Array Auto.Lemma) : MetaM TFF.Problem := do
  let (query, _) ← monomorphizeWithOptionalFacts lemmas inhs
    (@id (Auto.Reif.ReifM TFF.Problem) do
      let s ← get
      let u ← Auto.computeMaxLevel s.facts
      (do
        let (problem, _) ← prepareFirstOrderProblem s.facts s.inhTys s.inds
        return problem
        : Auto.LamReif.ReifM TFF.Problem).run' {u := u})
  return query

end VampireHammer

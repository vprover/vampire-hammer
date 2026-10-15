import VampireHammer.Backend.Metadata
import VampireHammer.Backend.Resolution
import VampireHammer.Backend.Factoring
import VampireHammer.Backend.Equality
import VampireHammer.Backend.Rewriting
import VampireHammer.Backend.CertifiedRewriting
import VampireHammer.Backend.Permutation
import VampireHammer.Backend.Preprocessing
import VampireHammer.Backend.Definitions
import VampireHammer.Backend.Avatar
import VampireHammer.Backend.AvatarConversion
import VampireHammer.Backend.Sat
import VampireHammer.Backend.Simplification
import VampireHammer.Backend.Naming
import VampireHammer.Backend.GlobalSubsumption
import VampireHammer.Backend.HigherOrder
import VampireHammer.Backend.HigherOrderBoolean
import VampireHammer.Backend.HigherOrderQuantifier
import VampireHammer.Backend.HigherOrderChoice
import VampireHammer.Backend.HigherOrderAxiom
import VampireHammer.Backend.PredicateElimination

/-!
The explicit mapping from Vampire rule names to reconstruction handlers.

Annotation decoders are in `Backend.Metadata`; each handler has its own module.
Dispatch returns `none` when a certificate or phase is unsupported. It never
calls `grind`: the main backend controls the single fallback and constructs
the local theorem over parent hypotheses.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Dispatch post-CNF calculus, explicit AC, AVATAR, and SAT inferences.
Each branch decodes its certificate and invokes exactly one handler. The
phase guard prevents a formula-stage node from being interpreted as a stored
clause. A handler returning `none` leaves the fallback decision to the caller. -/
private def dispatchClause (input : RuleInput) (inference : Inference) :
    MetaM (Option (String × Expr)) := do
  if !storesClauseForm input then return none
  match inference.rule with
  | "global_subsumption" =>
    return (← globalSubsumption input).map ("global subsumption", ·)
  | "predicate_elimination" =>
    return (← predicateElimination input).map ("predicate elimination", ·)
  | "resolution" => do
    let some info := inference.resolution? | return none
    return (← resolution input info).map ("resolution", ·)
  | "extensionality_resolution" => do
    let some info := inference.extensionalityResolution? | return none
    return (← resolution input info).map ("extensionality resolution", ·)
  | "forward_literal_rewriting" => do
    let some info := inference.forwardLiteralRewriting? | return none
    return (← forwardLiteralRewriting input info).map ("forward literal rewriting", ·)
  | "unit_resulting_resolution" => do
    let some info := inference.unitResultingResolution? | return none
    return (← unitResultingResolution input info).map ("unit-resulting resolution", ·)
  | "constrained_resolution" => do
    let some info := inference.constrainedResolution? | return none
    return (← constrainedResolution input info).map ("constrained resolution", ·)
  | "backward_subsumption_resolution" => do
    let some info := inference.forwardSubsumptionResolution? | return none
    return (← forwardSubsumptionResolution input info).map ("backward subsumption", ·)
  | "subsumption_equality_resolution" => do
    let some info := inference.equalityResolution? | return none
    return (← equalityResolution input info).map ("subsumption equality resolution", ·)
  | "condensation" => do
    let some info := inference.condensation? | return none
    return (← condensation input info).map ("condensation", ·)
  | "forward_subsumption_resolution" => do
    let some info := inference.forwardSubsumptionResolution? | return none
    return (← forwardSubsumptionResolution input info).map ("forward subsumption", ·)
  | "factoring" => do
    let some info := inference.factoring? | return none
    return (← factoring input info).map ("factoring", ·)
  | "duplicate_literal_removal" =>
    return (← duplicateLiteralRemoval input).map ("duplicate literal removal", ·)
  | "equality_resolution" => do
    let some info := inference.equalityResolution? | return none
    if let some proof ← equalityResolution input info then
      return some ("equality resolution", proof)
    return (← constrainedEqualityResolution input info).map ("constrained equality resolution", ·)
  | "trivial_inequality_removal" =>
    if let some proof ← trivialInequalityRemoval input then
      return some ("trivial inequality removal", proof)
    return (← higherOrderBoolean input).map ("Boolean false literal removal", ·)
  | "equality_factoring" => do
    let some info := inference.equalityFactoring? | return none
    if let some proof ← equalityFactoring input info then
      return some ("equality factoring", proof)
    return (← constrainedEqualityFactoring input info).map ("constrained equality factoring", ·)
  | "superposition" => do
    let some info := inference.superposition? | do
      trace[vampire.replay] "superposition {input.step.name} declined: unsupported or incomplete metadata"
      return none
    return (← superposition input info).map ("superposition", ·)
  | "backward_demodulation" | "forward_subsumption_demodulation"
  | "backward_subsumption_demodulation" | "inner_rewriting" | "constrained_superposition" => do
    let some info := inference.certifiedRewrite? | return none
    return (← certifiedRewriting input info).map (inference.rule, ·)
  | "forward_demodulation" => do
    let some info := inference.forwardDemodulation? | return none
    return (← forwardDemodulation input info).map ("forward demodulation", ·)
  | "associativity_commutativity" => do
    let some positions := inference.associativityCommutativity? | return none
    return (← associativityCommutativity input positions).map ("clause permutation", ·)
  | "rat" | "avatar_sat_refutation" =>
    return (← avatarSatByBVDecide input).map ("AVATAR SAT", ·)
  | "sat_conversion" =>
    if inference.hasAvatarMap then
      let some mappings := inference.avatarMap? | return none
      return (← avatarConversion input mappings).map ("AVATAR conversion", ·)
    else
      return (← avatarIdentity input).map ("AVATAR identity", ·)
  | "avatar_component_clause" =>
    return (← avatarComponentClause input).map ("AVATAR component", ·)
  | "avatar_split_clause" =>
    return (← avatarSplitClause input).map ("AVATAR split", ·)
  | "definition_unfolding" =>
    if input.parents.size == 2 && !inference.info.isEmpty then
      let some info := inference.certifiedRewrite? | return none
      return (← certifiedRewriting input info).map ("definition unfolding rewrite", ·)
    return (← definitionUnfolding input).map ("definition unfolding", ·)
  | "cnf_transformation" =>
    return (← splittingComponentClause input).map ("general splitting component", ·)
  | "general_splitting" =>
    return (← generalSplitting input).map ("general splitting", ·)
  | "inequality_splitting" =>
    return (← definitionalClauseTransport input "inequality splitting").map
      ("inequality splitting", ·)
  | "equality_proxy_replacement" =>
    return (← definitionalClauseTransport input "equality proxy replacement").map
      ("equality proxy replacement", ·)
  | "equality_proxy_axiom" =>
    return (← equalityProxyAxiom input).map ("equality proxy axiom", ·)
  | "avatar_contradiction_clause" =>
    return (← avatarContradictionClause input).map ("AVATAR contradiction", ·)
  | _ => return none

/-- Definition and renaming nodes have their own certificates or structural
checks. They are tried before the general preprocessing identity fast path. -/
private def dispatchDefinition (input : RuleInput) (inference : Inference) :
    MetaM (Option (String × Expr)) := do
  match inference.rule with
  | "avatar_definition" =>
    let some info := inference.avatarDefinition? | return none
    return (← avatarDefinition input info).map ("AVATAR definition", ·)
  | "predicate_definition_introduction" =>
    let some info := inference.predicateDefinition? | return none
    return (← predicateDefinition input info).map ("predicate definition", ·)
  | "function_definition" | "fool_ite_definition" | "general_splitting_component_introduction"
  | "inequality_splitting_name_introduction" | "equality_proxy_definition" =>
    let some info := inference.predicateDefinition? | return none
    return (← symbolDefinition input info).map (inference.rule, ·)
  | "unused_predicate_definition_removal" =>
    return (← unusedPredicateDefinitionRemoval input).map ("unused predicate definition removal", ·)
  | "definition_folding" =>
    return (← definitionFolding input).map ("definition folding", ·)
  | "rectify" =>
    return (← rectify input).map ("rectify", ·)
  | "pure_predicate_removal" =>
    return (← purePredicateRemoval input).map ("pure predicate removal", ·)
  | _ => return none

/-- Certificate-free single-parent rules. They are phase-independent: each
handler reads a clause parent through its parser formula, and the caller
returns a clause-phase result to clause form. -/
private def dispatchSimplification (input : RuleInput) (inference : Inference) :
    MetaM (Option (String × Expr)) := do
  match inference.rule with
  | "reorient_equations" =>
    return (← reorientEquations input).map ("reorient equations", ·)
  | "closure" =>
    return (← closure input).map ("closure", ·)
  | "true_and_false_elimination" =>
    return (← reduceFalseTrue input).map ("true/false elimination", ·)
  | "consistent_polarity_flipping" =>
    return (← polarityFlipping input).map ("polarity flipping", ·)
  | _ => return none

/-- The complete list of logical transformations delegated to VampLean.
An unrecognized name can only use the checked identity case; it cannot select
an arbitrary tactic or enter the clause-calculus handlers through this path. -/
private def dispatchPreprocessing (input : RuleInput) (inference : Inference) :
    MetaM (Option Expr) := do
  match inference.rule with
  | "flattening" | "remove_tauto" | "remove_tautologies"
  | "ennf_transformation" | "nnf_transformation" | "cnf_transformation" =>
    preprocessWithVampLean input inference.rule
  | _ => preprocessingIdentity input

/-- Route one inference to its direct handler, preserving the replay phases.

The order is explicit: definitions/renaming, certificate-free
simplifications, logical preprocessing (including
unchanged formulas), Skolemization, then clause and AVATAR/SAT rules. Formula
handlers check their parent representation; clause dispatch additionally
requires the decoder's post-CNF mark. `cnf_transformation` is allowed to prove
an ordinary formula here because `Backend.reconstruct` subsequently performs
the one conversion into stored clause form.

A successful result carries a trace label and a proof. `none` means no direct
handler accepted the certificate: the caller may then invoke the single
`fallbackToGrind` boundary. This function does not introduce parent hypotheses,
convert stored representations, or call fallback tactics. -/
def dispatch (input : RuleInput) (inference : Inference) :
    MetaM (Option (String × Expr)) := do
  let rule := inference.rule
  let instantiation : MetaM (Option (String × Expr)) := do
    let some substitutions := inference.higherOrderInstantiation? | return none
    return (← higherOrderInstantiation input substitutions).map (rule, ·)
  match rule with
  | "Hilbertian_choice_axiom_instance" | "hilbertian_choice_axiom_instance" =>
    let some info := inference.choiceAxiom? | throwError "incomplete choice certificate for `{input.step.name}`"
    let some proof ← higherOrderChoice input info | throwError "invalid choice instance `{input.step.name}`"
    return some ("Hilbert choice", proof)
  | "functional_extensionality_axiom" =>
    let some info := inference.functionalExtensionality? | throwError "incomplete extensionality certificate for `{input.step.name}`"
    let some proof ← higherOrderFunctionalExtensionality input info | throwError "invalid extensionality axiom `{input.step.name}`"
    return some ("functional extensionality axiom", proof)
  | "beta-eta_normalization" | "beta_eta_normalization" =>
    return (← higherOrderNormalization input).map (rule, ·)
  | "pi_proxy_clausification" | "pi_proxy_clausification_(simplifying)" =>
    return (← higherOrderPi input).map (rule, ·)
  | "sigma_proxy_clausification" | "sigma_proxy_clausification_(simplifying)" =>
    let some info := inference.quantifierWitness? | return none
    return (← higherOrderSigma input info).map (rule, ·)
  | "flex-flex_simplification" | "flex_flex_simplification" =>
    let some substitutions := inference.higherOrderInstantiation? | return none
    return (← higherOrderFlexFlex input substitutions).map (rule, ·)
  | "leibniz_equality_elimination" =>
    let some substitutions := inference.higherOrderInstantiation? | return none
    return (← higherOrderBooleanInstantiation input substitutions).map (rule, ·)
  | "fool_paramodulation" | "cases_simplifying" =>
    let some info := inference.booleanCase? | return none
    return (← higherOrderBooleanCase input info).map (rule, ·)
  | "boolean_simplification" | "bool_equality_to_disequality"
  | "not_proxy_clausification" | "and_proxy_clausification" | "or_proxy_clausification"
  | "imp_proxy_clausification" | "iff_proxy_clausification" | "xor_proxy_clausification"
  | "equality_proxy_clausification" | "not_proxy_clausification_(simplifying)"
  | "and_proxy_clausification_(simplifying)" | "or_proxy_clausification_(simplifying)"
  | "imp_proxy_clausification_(simplifying)" | "iff_proxy_clausification_(simplifying)"
  | "xor_proxy_clausification_(simplifying)" | "equality_proxy_clausification_(simplifying)" =>
    return (← higherOrderBoolean input).map (rule, ·)
  | "heuristic_instantiation" =>
    if let some info := inference.quantifierInstance? then
      return (← higherOrderQuantifierInstance input info).map (rule, ·)
    instantiation
  | "primitive_instantiation" | "imitation" | "projection" => instantiation
  | "positive_extensionality" | "argument_congruence" =>
    return (← higherOrderEquality input rule).map (rule, ·)
  | "fool_elimination" =>
    if let some proof ← foolElimination input then return some ("FOOL elimination", proof)
    return (← higherOrderBoolean input).map ("FOOL Boolean normalization", ·)
  | "negative_extensionality" =>
    let some info := inference.negativeExtensionality? | return none
    return (← negativeExtensionality input info).map ("negative extensionality", ·)
  | "fool_exhaustiveness_axiom" =>
    return (← foolExhaustiveness input).map ("FOOL exhaustiveness", ·)
  | "fool_distinctness_axiom" =>
    return (← foolDistinctness input).map ("FOOL distinctness", ·)
  | "theory_tautology_sat_conflict" =>
    return (← theoryTautologySatConflict input).map ("EUF conflict", ·)
  | _ =>
    if let some result ← dispatchDefinition input inference then
      return some result
    if let some result ← dispatchSimplification input inference then
      return some result
    if let some proof ← dispatchPreprocessing input inference then
      return some ("VampLean", proof)
    match rule with
    | "skolemize" | "skolemisation" =>
      let some info := inference.skolemization? | return none
      let some proof ← skolemize input info | return none
      -- The witnesses are `Classical.choose` terms here and Skolem lets in the
      -- target. Check their agreement with let unfolding enabled, then state
      -- the proof at the displayed target; other rules keep those lets folded.
      let some proof ← withConfig (fun config => { config with zetaDelta := true }) <|
          asExpectedType proof input.target
        | return none
      return some ("skolemization", proof)
    | _ => dispatchClause input inference

end VampireHammer.Backend

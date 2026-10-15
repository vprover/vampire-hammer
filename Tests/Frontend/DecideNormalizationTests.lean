import VampireHammer.Export.Monomorphization

open Lean Meta Elab Tactic

set_option linter.unusedVariables false

-- `decide` resolves to `Decidable.decide`. Preserve it until Auto's checked
-- rewrite can remove the proof-dependent Decidable recursor before reification.
elab "check_decide_normalization " hypothesis:term : tactic => withMainContext do
  let lemma ← Auto.Prep.elabLemma hypothesis (.leaf "decide regression")
  let normalized ← VampireHammer.SourceNormalization.normalizeLemma lemma
  unless normalized.type.getUsedConstants.contains ``decide do
    throwError "source normalization expanded decide before its checked rewrite"
  unless ← isDefEq (← inferType normalized.proof) normalized.type do
    throwError "source normalization changed the checked premise type"
  let prepared ← VampireHammer.SourceNormalization.prepareForMonomorphization #[normalized]
  unless prepared.size == 1 &&
      prepared[0]!.type.getUsedConstants.contains ``Auto.Bool.ofProp do
    throwError "decide was not rewritten to the supported logical primitive"
  unless ← isDefEq (← inferType prepared[0]!.proof) prepared[0]!.type do
    throwError "checked decide rewriting lost its proof"
  let inhs ← Auto.Inhabitation.getInhFactsFromLCtx
  let _ ← VampireHammer.Export.Internal.monomorphizeWithOptionalFacts #[normalized] inhs
    fun state => do
      let action : Auto.LamReif.ReifM Unit := do
        for fact in state.facts do
          let (sort, _) ← Auto.LamReif.reifTermCheckType fact.type
          unless sort == .base .prop do throwError "reified premise is not a proposition"
      let _ ← (action.run' {u := ← Auto.computeMaxLevel state.facts}).run state
      pure ()

example (p : Prop) [Decidable p] (h : decide p = false) : True := by
  check_decide_normalization h
  trivial

-- Both branches use the same logical primitive; no assumption about which
-- branch the local Decidable instance chooses may be introduced.
example (p : Prop) [Decidable p] (h : decide p = true) : True := by
  check_decide_normalization h
  trivial

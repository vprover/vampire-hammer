import Auto.Tactic

open Lean Meta Elab Tactic

namespace VampireHammer

initialize registerTraceClass `vampire.bridge

/-- The only inference pattern implemented by the temporary bridge backend. -/
theorem exampleRefutation {α : Sort u} {P Q : α → Prop} {a : α}
    (step : ∀ x, P x → Q x) (premise : P a) (negative : ¬ Q a) : False :=
  negative (step a premise)

/-- Construct a proof from the callback premises, independently of their names
and order. This is a bridge smoke test, not a Vampire certificate checker. -/
def exampleBackend (lemmas : Array Auto.Lemma) (_inhs : Array Auto.Lemma) : MetaM Expr := do
  for step in lemmas do
    for premise in lemmas do
      for negative in lemmas do
        let saved ← saveState
        try
          let proof ← mkAppM ``exampleRefutation #[step.proof, premise.proof, negative.proof]
          let proof ← instantiateMVars proof
          if proof.hasExprMVar || proof.hasLevelMVar then
            throwError "Unresolved metavariables in bridge proof"
          unless ← isDefEq (← inferType proof) (mkConst ``False) do
            throwError "Bridge backend did not construct a proof of False"
          trace[vampire.bridge] "Callback proof: {proof}"
          return proof
        catch _ =>
          saved.restore
  throwError "Bridge backend: expected premises of the form (∀ x, P x → Q x), P a, and ¬ Q a"

/-- Close the goal through lean-auto's preprocessing and native proof bridge.
No external prover, exported files, or general-purpose proof search is used. -/
syntax (name := vampireBridge) "vampire_bridge" Auto.hints : tactic

elab_rules : tactic
  | `(vampireBridge| vampire_bridge $hints) => withMainContext do
    let (binders, goal) ← (← getMainGoal).intros
    let [negGoal] ← goal.apply (mkConst ``Classical.byContradiction)
      | throwError "Could not create a refutation goal"
    let (negHyp, absurd) ← negGoal.intro1
    replaceMainGoal [absurd]
    withMainContext do
      let (lemmas, inhs) ← Auto.collectAllLemmas hints #[] (binders.push negHyp)
      let proof ← Auto.runNativeProverWithAuto (← Elab.Term.getDeclName?)
        exampleBackend lemmas inhs
      let proof ← instantiateMVars proof
      if proof.hasExprMVar || proof.hasLevelMVar then
        throwError "Unresolved metavariables in lean-auto's returned proof"
      absurd.assign proof

end VampireHammer

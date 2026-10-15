import Auto.Tactic
import VampireHammer.Replay.Diagnostics
import VampireHammer.Export.SearchBudget


register_option vampire.directProof : Bool := {
  defValue := true
  descr := "Try to close the goal from the selected facts without translation before calling Vampire"
}

register_option vampire.directProofHeartbeats : Nat := {
  defValue := 2000
  descr := "Shared heartbeat allowance for optional direct proof attempts (0 disables them)"
}

namespace VampireHammer.Export.Internal

open Lean Meta

/-- Eliminate at most eight variables using selected equality proofs, then
try reflexivity. Lean's dependent substitution updates implicit parameters and
transports proof fields too; first-order specialization cannot retain these
connections. No unselected hypothesis is used to close the goal. -/
private def proveBySelectedSubstitution? (target : Expr) (facts : Array Auto.Lemma) :
    MetaM (Option Expr) := do
  let saved ← saveState
  try
    let candidate ← mkFreshExprMVar target .syntheticOpaque
    let mut goal := candidate.mvarId!
    let mut substitution : FVarSubst := {}
    let mut count := 0
    for fact in facts do
      if count >= 8 then break
      unless fact.params.isEmpty do continue
      let proof := substitution.apply fact.proof
      let changed ← goal.withContext do
        let type ← inferType proof
        let some (_, left, right) := type.eq? | return none
        unless left.isFVar || right.isFVar do return none
        let stepSaved ← saveState
        try
          let asserted ← goal.assert `selectedEquality type proof
          let (hypothesis, asserted) ← asserted.intro1
          let (nextSubstitution, nextGoal) ← substEq asserted hypothesis substitution
          return some (nextSubstitution, nextGoal)
        catch error =>
          trace[vampire] "Selected equality substitution skipped: {error.toMessageData}"
          stepSaved.restore
          return none
      if let some (nextSubstitution, nextGoal) := changed then
        substitution := nextSubstitution
        goal := nextGoal
        count := count + 1
    if count == 0 then throwError "no selected equality"
    if (← goal.getType).heq?.isSome then goal.hrefl else goal.refl
    let proof ← instantiateMVars candidate
    if proof.hasMVar then throwError "incomplete substitution proof"
    return some proof
  catch error =>
    trace[vampire] "Selected equality substitution did not close the goal: {error.toMessageData}"
    saved.restore
    return none


/-- Constructor equalities with dependent proof fields may lose their shared
head during first-order specialization. Prove a simple injectivity equivalence
using Lean's no-confusion principle and equality substitution instead. Only
newly introduced branch hypotheses are used, respecting explicit hints. -/
private def proveConstructorEquivalence? (target : Expr) : MetaM (Option Expr) := do
  let target ← instantiateMVars target
  let sides? := match target.iff? with
    | some sides => some sides
    | none => match target.eq? with
      | some (type, left, right) => if type == mkSort .zero then some (left, right) else none
      | none => none
  let some (left, right) := sides? | return none
  let env ← getEnv
  let isConstructorEquality := fun proposition =>
    match proposition.eq? with
    | some (_, a, b) =>
      a.getAppFn.isConst && b.getAppFn.isConst &&
        match env.find? a.getAppFn.constName!, env.find? b.getAppFn.constName! with
        | some (.ctorInfo first), some (.ctorInfo second) => first.induct == second.induct
        | _, _ => false
    | none => false
  unless isConstructorEquality left || isConstructorEquality right do return none
  let saved ← saveState
  try
    let candidate ← mkFreshExprMVar target .syntheticOpaque
    let mut goal := candidate.mvarId!
    if target.iff?.isNone then
      let [equivalence] ← goal.apply (mkConst ``propext)
        | throwError "unexpected proposition extensionality result"
      goal := equivalence
    let branches ← goal.apply (mkConst ``Iff.intro)
    unless branches.length == 2 do throwError "unexpected equivalence branches"
    for branch in branches do
      let (hypothesis, body) ← branch.intro1
      body.withContext do
        let hypothesisType ← instantiateMVars (← hypothesis.getType)
        if isConstructorEquality hypothesisType then
          match ← injection body hypothesis with
          | .solved => pure ()
          | .subgoal remaining equalities _ => remaining.withContext do
            let mut closed := false
            for equality in equalities do
              if ← isDefEq (← equality.getType) (← remaining.getType) then
                remaining.assign (mkFVar equality)
                closed := true
                break
            unless closed do throwError "injection did not supply the conclusion"
        else if (← whnf hypothesisType).isConstOf ``False then
          body.assign (mkApp2 (mkConst ``False.elim [.zero]) (← body.getType) (mkFVar hypothesis))
        else
          let (_, body) ← substEq body hypothesis
          body.refl
    let proof ← instantiateMVars candidate
    if proof.hasMVar then throwError "incomplete constructor equivalence proof"
    trace[vampire] "Closed constructor equivalence by checked injection and substitution"
    return some proof
  catch error =>
    trace[vampire] "Constructor equivalence did not close the goal: {error.toMessageData}"
    saved.restore
    return none

/-- Discharge at most eight application premises by exact collected facts.
No local hypothesis is consulted unless it belongs to the selected fact set. -/
private def dischargeSelectedPremises (goals : List MVarId) (facts : Array Auto.Lemma) :
    MetaM Bool := do
  if goals.length > 8 then return false
  for goal in goals.reverse do
    if ← goal.isAssigned then continue
    let mut closed := false
    for fact in facts[:min 64 facts.size] do
      let saved ← saveState
      try
        let levels ← fact.params.mapM fun _ => mkFreshLevelMVar
        let fact := fact.instantiateLevelParamsArray levels
        if ← isDefEq (← inferType fact.proof) (← goal.getType) then
          goal.assign fact.proof
          closed := true
          break
      catch _ => pure ()
      saved.restore
    unless closed do return false
  return true

/-- Different constructors of one inductive cannot be equal. Use only a
selected equality proof; the no-confusion principle supplies the contradiction. -/
private def proveSelectedConstructorClash? (target : Expr) (facts : Array Auto.Lemma) :
    MetaM (Option Expr) := do
  let env ← getEnv
  for fact in facts[:min 64 facts.size] do
    let some (_, left, right) := fact.type.eq? | continue
    let .const leftName _ := left.getAppFn | continue
    let .const rightName _ := right.getAppFn | continue
    if leftName == rightName then continue
    let some (.ctorInfo first) := env.find? leftName | continue
    let some (.ctorInfo second) := env.find? rightName | continue
    unless first.induct == second.induct do continue
    let saved ← saveState
    try
      let candidate ← mkFreshExprMVar target .syntheticOpaque
      let goal ← candidate.mvarId!.assert `selectedConstructorEquality fact.type fact.proof
      let (hypothesis, goal) ← goal.intro1
      match ← injection goal hypothesis with
      | .solved =>
        let proof ← instantiateMVars candidate
        unless proof.hasMVar do return some proof
      | _ => pure ()
    catch _ => pure ()
    saved.restore
  return none

/-- Try reflexivity or an exact application of a collected fact before export.
This also instantiates universal facts at the goal's actual parameters, even
when their types are dependent. Unsolved premises are not guessed at. Failed
applications restore the metavariable state, and only the selected facts are
considered. -/
private def compatibleConclusion (target factType : Expr) : MetaM Bool := do
  let mut conclusion := factType.consumeMData
  while conclusion.isForall do conclusion := conclusion.bindingBody!.consumeMData
  if let (.const first _, .const second _) := (target.getAppFn, conclusion.getAppFn) then
    let env ← getEnv
    if first != second && (env.find? first).any (·.isInductive) &&
        (env.find? second).any (·.isInductive) then return false
  return true

private def proveWithoutTranslationCore (target : Expr) (facts : Array Auto.Lemma) :
    MetaM (Option Expr) := do
  let saved ← saveState
  try
    let candidate ← mkFreshExprMVar target .syntheticOpaque
    candidate.mvarId!.refl
    let proof ← instantiateMVars candidate
    unless proof.hasMVar do return some proof
  catch _ => pure ()
  saved.restore
  for fact in facts do
    unless ← compatibleConclusion target fact.type do continue
    let saved ← saveState
    try
      let levels ← fact.params.mapM fun _ => mkFreshLevelMVar
      let fact := fact.instantiateLevelParamsArray levels
      let candidate ← mkFreshExprMVar target .syntheticOpaque
      let remaining ← candidate.mvarId!.apply fact.proof
      if ← dischargeSelectedPremises remaining facts then
        let proof ← instantiateMVars candidate
        unless proof.hasMVar do
          trace[vampire] "Closed goal by application of a collected source fact"
          return some proof
    catch _ => pure ()
    saved.restore
  if let some proof ← proveSelectedConstructorClash? target facts then return some proof
  if let some proof ← proveBySelectedSubstitution? target facts then return some proof
  proveConstructorEquivalence? target

/-- Optional direct closure shares one budget across reflexivity, applications,
premise discharge and structural handlers. Exhaustion leaves the main route
the original goal and facts, with no speculative assignments. -/
def proveWithoutTranslation? (target : Expr) (facts : Array Auto.Lemma) : MetaM (Option Expr) := do
  let budget ← SearchBudget.create (vampire.directProofHeartbeats.get (← getOptions))
  return (← budget.run (proveWithoutTranslationCore target facts)).getD none

end VampireHammer.Export.Internal

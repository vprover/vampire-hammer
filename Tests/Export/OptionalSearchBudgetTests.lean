import VampireHammer
import VampireHammer.Export.SearchBudget

open Lean Meta Elab Tactic VampireHammer.Export

-- Synthetic allocation increments make these resource tests deterministic.
-- The proof goals are still checked normally; no timeout admits a proof.
elab "check_search_budget" : tactic => withMainContext do
  -- Optional premise collection must not swallow cancellation or extend the
  -- enclosing heartbeat deadline, even when it catches a local timeout.
  let interrupted ← tryCatchRuntimeEx
    (do
      let _ ← VampireHammer.SiblingLemmas.attempt 1000 (throwInterruptException : MetaM Unit)
      pure false)
    (fun error => if error.isInterrupt then pure true else throw error)
  unless interrupted do throwError "premise selection swallowed cancellation"
  let start ← IO.getNumHeartbeats
  let propagated ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun context =>
      { context with initHeartbeats := start, maxHeartbeats := 1000 }) do
        let _ ← VampireHammer.SiblingLemmas.attempt 100000 do
          IO.addHeartbeats 2000
        pure false)
    (fun error => if error.isMaxHeartbeat then pure true else throw error)
  unless propagated do throwError "premise selection extended the caller's deadline"

  let allowance ← SearchAllowance.create 100
  let first ← allowance.run (do IO.addHeartbeats 20000; pure true)
  -- Required work between optional passes must not consume their allowance.
  IO.addHeartbeats 500000
  let second ← allowance.run (do IO.addHeartbeats 20000; pure true)
  unless first == some true && second == some true do
    throwError "required work expired an unused optional allowance"
  let last ← allowance.run (do IO.addHeartbeats 100000; pure true)
  unless last.isNone do throwError "optional passes restarted their cumulative allowance"

  let budget ← SearchBudget.create 30
  for _ in [:2] do
    let result ← budget.run (do IO.addHeartbeats 10000; pure true)
    unless result == some true do throwError "a fresh shared budget was exhausted too early"
  let result ← budget.run (do IO.addHeartbeats 20000; pure true)
  unless result.isNone do throwError "attempts restarted the shared heartbeat clock"

  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let budget ← SearchBudget.create 10
  let result ← budget.run (do
    pending.mvarId!.assign (mkNatLit 7)
    IO.addHeartbeats 20000
    pure true)
  unless result.isNone && !(← pending.mvarId!.isAssigned) do
    throwError "a timed-out attempt leaked its metavariable assignment"

  let budget ← SearchBudget.create 0
  let ran ← IO.mkRef false
  let _ ← budget.run (do ran.set true; pure ())
  if ← ran.get then throwError "a disabled search executed its action"

  let budget ← SearchBudget.create 10
  let interrupted ← tryCatchRuntimeEx
    (do
      let _ ← budget.run (throwInterruptException : MetaM Unit)
      pure false)
    (fun error => if error.isInterrupt then pure true else throw error)
  unless interrupted do throwError "optional search swallowed cancellation"

  let propagated ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun context =>
      { context with initHeartbeats := 0, maxHeartbeats := 1 }) do
        let budget ← SearchBudget.create 10
        let _ ← budget.run (pure ())
        pure false)
    (fun error => if error.isMaxHeartbeat then pure true else throw error)
  unless propagated do throwError "optional search swallowed the caller's timeout"

  let start ← IO.getNumHeartbeats
  let propagated ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun context =>
      { context with initHeartbeats := start, maxHeartbeats := 10000 }) do
        let budget ← SearchBudget.create 100
        let _ ← budget.run (do IO.addHeartbeats 12000; pure ())
        pure false)
    (fun error => if error.isMaxHeartbeat then pure true else throw error)
  unless propagated do throwError "a local allowance extended the caller's deadline"

example : True := by
  check_search_budget
  trivial

structure BudgetMap where
  apply : Nat → Nat

structure OtherBudgetMap where
  apply : Nat → Nat

abbrev BudgetMapAlias := BudgetMap

elab "check_data_witnesses " rule:term ", " wrong:term ", " right:term : tactic =>
  withMainContext do
    let rule ← Term.elabTerm rule none
    let wrong ← Term.elabTerm wrong none
    let right ← Term.elabTerm right none
    let premise : Auto.Lemma := ⟨⟨rule, ← inferType rule, .leaf "budget test"⟩, #[]⟩
    let witnesses ← #[wrong, right].mapM fun value => do
      return { value, type := ← inferType value, params := #[], label := "budget test" :
        VampireHammer.Export.DataWitnesses.Witness }
    let target ← (← getMainGoal).getType
    let disabled ← withOptions (·.set `vampire.dataWitnessHeartbeats (0 : Nat)) <|
      VampireHammer.Export.DataWitnesses.instantiate #[premise] witnesses #[target]
    unless disabled.isEmpty do throwError "zero witness budget generated optional facts"
    let facts ← VampireHammer.Export.DataWitnesses.instantiate #[premise] witnesses #[target]
    let some fact := facts.find? (·.type == target)
      | throwError "compatible aliased witness was lost after an incompatible structure"
    unless ← isTypeCorrect fact.proof do throwError "witness fact is not type correct"
    (← getMainGoal).assign fact.proof

example (P : BudgetMap → Prop) (rule : ∀ m, P m)
    (_wrong : OtherBudgetMap) (right : BudgetMapAlias) : P right := by
  check_data_witnesses rule, _wrong, right

-- Cheap selected applications and dependent substitution still close without
-- launching an external process under the new shared allowance.
set_option vampire.executable "/missing-vampire-budget-test"
set_option vampire.attributeLemmas false
example (P Q : Prop) (p : P) (step : P → Q) : Q := by
  vampire [p, step]

example {α : Type} {β : α → Type} (x y : α) (h : x = y)
    (f : (a : α) → β a) : HEq (f x) (f y) := by
  vampire [h]

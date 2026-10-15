import VampireHammer

open Lean Meta Elab Tactic
open VampireHammer.Export.Internal

set_option linter.unusedVariables false
set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

private def localLemma (name : Name) (label : String) : TacticM Auto.Lemma := do
  let some declaration := (← getLCtx).findFromUserName? name
    | throwError "missing local premise {name}"
  return ⟨⟨declaration.toExpr, declaration.type, .leaf label⟩, #[]⟩

private def proveWithOptional (labelPrefix : String) : TacticM Unit := withMainContext do
  let lemmas ← #[
    localLemma `hp "required positive hypothesis",
    localLemma `hn "required negative hypothesis",
    localLemma `law (labelPrefix ++ " usable transfer"),
    localLemma `unsupported (labelPrefix ++ " unsupported empty-domain fact")].mapM id
  let proof ← replayVampireWithAuto lemmas #[]
  (← getMainGoal).assign proof

-- Unsupported discovered facts may be omitted, while an independent usable
-- fact from the same selector must remain available for the proof.
theorem optional_sibling_thf (P Q : Prop) (ε : Type) (F : ε → Prop)
    (hp : P) (hn : ¬Q) (law : P → Q) (unsupported : ∀ x, F x) : False := by
  run_tac proveWithOptional VampireHammer.SiblingLemmas.labelPrefix

theorem optional_suggested_thf (P Q : Prop) (ε : Type) (F : ε → Prop)
    (hp : P) (hn : ¬Q) (law : P → Q) (unsupported : ∀ x, F x) : False := by
  run_tac proveWithOptional VampireHammer.SuggestedLemmas.labelPrefix

-- The same unsupported empty-domain fact is required when explicitly requested.
example (P Q : Prop) (ε : Type) (F : ε → Prop)
    (hp : P) (hn : ¬Q) (law : P → Q) (unsupported : ∀ x, F x) : False := by
  fail_if_success run_tac proveWithOptional "explicit hint"
  exact hn (law hp)

#print axioms optional_sibling_thf
#print axioms optional_suggested_thf

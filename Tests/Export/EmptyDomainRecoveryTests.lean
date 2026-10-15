import VampireHammer
import VampireHammer.EmptyDomains

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

open Lean Meta Elab Tactic

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.directProof false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option linter.unusedVariables false

-- Recovery selects the actual composite type rather than the first few type
-- parameters in the context. Diagnostic formatting must retain that payload.
elab "check_missing_type " type:term : tactic => withMainContext do
  let type ← instantiateMVars (← Term.elabType type)
  let message ← VampireHammer.Export.missingDomainMessage "THF export: missing" type
  let message ← addMessageContext message
  let candidates ← VampireHammer.EmptyDomains.missingCandidates message
  unless candidates == #[type] do throwError "lost the precise missing type"

example {α β γ δ ε : Type} (n : Nat) (S : α → Prop) : True := by
  check_missing_type Fin n
  check_missing_type Subtype S
  trivial

-- Test checked simplification of hypotheses and nested composite domains,
-- independently of external search and source-definition alignment.
elab "close_empty " type:term ", " proof:term : tactic => withMainContext do
  let type ← Term.elabType type
  let proof ← Term.elabTerm proof none
  let result ← VampireHammer.EmptyDomains.closeEmpty (← getMainGoal) type proof.fvarId!
  setGoals (result.toList)

theorem empty_hypothesis {α : Type} (empty : ¬Nonempty α) (Q : Prop)
    (h : (∃ x : α, True) ∨ Q) : Q := by
  close_empty α, empty

theorem nested_empty_domain {α : Type} (empty : ¬Nonempty α)
    (P : ((α × Nat) × Nat) → Prop) : ∀ x, P x := by
  close_empty α, empty

-- Native-only export/replay for a domain which may genuinely be empty.
set_option vampire.outputPath "artifacts/ho-empty-fin.p" in
theorem empty_fin_quantifiers (n : Nat) (P : Fin n → Prop) :
    (∀ x, P x) ↔ ¬∃ x, ¬P x := by
  vampire

-- An unrelated sequence of type variables must not consume recovery's cap.
theorem targeted_empty_quantifiers {α β γ δ ε ζ : Type} (P : ζ → Prop) :
    (∀ x, P x) ↔ ¬∃ x, ¬P x := by
  vampire

set_option vampire.executable "Tests/testdata/scripts/mock-ho-gaveup.sh"
set_option vampire.outputPath "artifacts/ho-deferred-diagnostic.p"

#eval show IO Unit from do
  let path : System.FilePath := "artifacts/ho-deferred-diagnostic.p.events.jsonl"
  if ← path.pathExists then IO.FS.removeFile path

-- The first export lacks α, the nonempty retry reaches the solver and gives
-- up. Report the latter failure, and retain the former in the event history.
set_option vampire.decomposeGoals false in
example {α : Type} (P : α → Prop) (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : True := by
  run_tac withMainContext do
    let saved ← saveState
    let pending ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [pending.mvarId!]
    let message ← try
      evalTactic (← `(tactic| vampire [*]))
      pure "unexpected success"
    catch error => error.toMessageData.toString
    saved.restore
    unless message.contains "SZS status GaveUp" &&
        !message.contains "no known inhabitation evidence" do
      throwError "deferred witness masked its terminal error: {message}"
  trivial

#eval show IO Unit from do
  let events ← IO.FS.readFile "artifacts/ho-deferred-diagnostic.p.events.jsonl"
  unless events.contains "initial_error" && events.contains "terminal_error" &&
      events.contains "solver_result" do
    throw <| IO.userError "incomplete deferred witness history"

#print axioms empty_hypothesis
#print axioms nested_empty_domain
#print axioms empty_fin_quantifiers
#print axioms targeted_empty_quantifiers

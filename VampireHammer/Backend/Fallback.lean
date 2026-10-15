import VampireHammer.Backend.Common
import Auto.Tactic

/-!
The single `grind` fallback boundary.

Stored clause parents are temporarily converted to ordinary formulas. Source
facts and the canonical clause proofs are hidden where possible so `grind`
proves the individual reported step from its parents. The main reconstruction
entry point alone decides when a failed direct handler reaches this fallback.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic

register_option vampire.grindMaxHeartbeats : Nat := {
  defValue := 100000
  descr := "Heartbeat limit (in thousands) for each `grind` fallback step; 0 uses only the enclosing limit"
}
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Prove a fallback rule over temporary ordinary-formula parents.

Before CNF, parents already use their raw parser formulas. After a
`cnf_transformation`, only clause-form parents are converted here before
invoking `grind`; `reconstructDerivedBody` returns the result to clause form.

Calculus handlers apply Vampire's recorded substitutions directly, including
quantified AVATAR components. This fallback uses ordinary `grind` only when
no direct handler accepts the reported inference. Stored proof-DAG nodes
remain in their ordered `Clause.Holds` representation. -/
def fallbackToGrind (input : RuleInput) : MetaM Expr := do
  trace[vampire.replay] "fallback to `grind` for {input.target}"
  unless input.sourceProof?.isNone do
    throwError "internal error: attempted to reconstruct the input step `{input.step.name}` with `grind`"
  withFormulaParents input.parents 0 #[] fun _formulaParents => do
    -- Hide the source facts (a proof-local Skolem `let` depending on one keeps
    -- it visible) and the canonical clause-form parents, which must not be
    -- visible to `grind` alongside their ordinary formula counterparts.
    let clauseParents := input.parents.filterMap fun parent =>
      if parent.clauseForm then parent.proof.fvarId? else none
    let goalExpr ← mkGoalWithout input.target (input.sourceFVars ++ clauseParents)
    let goal := goalExpr
    -- One hard step must not consume the whole elaboration budget.
    let limit := vampire.grindMaxHeartbeats.get (← getOptions)
    let grind := do Lean.Elab.runTactic goal (← `(tactic| grind))
    let (remaining, _) ← if limit == 0 then grind else do
      -- Never extend the enclosing limit: cap the step at what is left of it.
      let context ← readThe Core.Context
      let used := (← IO.getNumHeartbeats) - context.initHeartbeats
      let stepLimit := if context.maxHeartbeats == 0 then limit * 1000
        else max 1 (min (limit * 1000) (context.maxHeartbeats - used))
      withTheReader Core.Context (fun context => { context with maxHeartbeats := stepLimit })
        (withCurrHeartbeats grind)
    unless remaining.isEmpty do
      throwError "`grind` left goals while replaying a Vampire step"
    let proof ← instantiateMVars (.mvar goalExpr)
    -- Tactics may unfold the proof-local lets while assigning their goal.
    -- Check that result with unfolding enabled, then state it at the original
    -- parser type. Ordinary clause rules deliberately keep named predicates
    -- and Skolem functions folded; comparing an expanded tactic result under
    -- that restricted configuration would otherwise reject a valid proof.
    let some proof ← withConfig (fun config => { config with zetaDelta := true }) <|
        asExpectedType proof input.target
      | throwError "fallback proof for `{input.step.name}` has the wrong result type"
    pure proof

end VampireHammer.Backend

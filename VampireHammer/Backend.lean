import VampireHammer.Backend.Dispatch
import VampireHammer.Backend.Fallback

/-!
The reconstruction entry point for one decoded Vampire step.

Rule selection lives in `Backend.Dispatch`. This file verifies source facts,
builds each derived step as a local lemma over fresh parent hypotheses, and
applies that lemma to the proof DAG. It also owns the one return-to-clause
conversion and invokes the single `grind` fallback when dispatch declines.

Importing this module preserves the existing `VampireHammer.Backend` API.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Verify that a TPTP input node denotes precisely its local source fact.

The local reconstruction context contains one readable hypothesis named
`factN` for each exported input. No inference is needed for an input node:
`isDefEq` checks the parsed formula against that hypothesis and returns it.
The actual lean-auto source proof is supplied only after the completed local
refutation has been built. -/

private def reconstructSource (input : RuleInput) : MetaM Expr := do
  let some sourceProof := input.sourceProof?
    | throwError "internal error: source reconstruction without a source proof"
  unless input.parents.isEmpty do
    throwError "TPTP input step `{input.step.name}` unexpectedly has proof parents"
  unless input.step.inference?.isNone do
    throwError "TPTP input step `{input.step.name}` unexpectedly has an inference annotation"
  let sourceType ← inferType sourceProof
  if ← isDefEq sourceType input.target then
    trace[vampire.replay] "source {input.step.name} (`{input.step.sourceFact?.getD "<unknown>"}`): verified the parsed formula against the local input hypothesis"
    return sourceProof
  -- The decoder right-associates `∨`, Vampire drops `¬¬`, and TPTP prints
  -- proposition equality as equivalence; the exported fact keeps Lean's spelling.
  trace[vampire.replay] "input boundary {input.step.name}: source {sourceType}; decoded {input.target}"
  let transported ← BackendPreprocessing.regroup sourceProof input.target
  -- Native Vampire printing may reorder/simplify logical terms beneath
  -- lambdas. Require checked equivalence in both directions at this boundary.
  let transported ← if transported.isSome then pure transported else
    higherOrderBooleanEquivalent sourceProof input.target
  let some regrouped := transported
    | throwError "TPTP input step `{input.step.name}` does not match local source fact `{input.step.sourceFact?.getD "<unknown>"}`"
  trace[vampire.replay] "source {input.step.name} (`{input.step.sourceFact?.getD "<unknown>"}`): transported the local input hypothesis"
  pure regrouped

/-- Prove one inference over the fresh parent hypotheses of its local lemma.
`dispatch` selects a direct handler; this function alone decides whether to
use `grind` and performs the final representation check/conversion. -/
private def reconstructDerivedBody (input : RuleInput) : MetaM Expr := do
  trace[vampire.replay] "derived step {input.step.name}: rule `{input.step.inference?.map (·.rule) |>.getD "<no rule>"}`, parents [{String.intercalate ", " (input.parents.map (·.parent.name)).toList}]"
  let useClauses := storesClauseForm input
  let direct? ← match input.step.inference? with
    | some inference => dispatch input inference
    | none => pure none
  let proof ← match direct? with
    | some (rule, proof) =>
      trace[vampire.replay] "{rule} directly reconstructed {input.step.name}"
      pure proof
    | none =>
      let proof ← fallbackToGrind input
      trace[vampire.replay] "`grind` reconstructed {input.step.name}"
      pure proof
  if useClauses then
    let some clauseProof ← toClauseForm proof input.target input.step.binders.size
      input.clauseLiterals? (storesAClause input) (avatarAtoms input)
      | throwError "could not convert reconstructed step `{input.step.name}` to clause form"
    pure clauseProof
  else
    unless ← isDefEq (← inferType proof) input.target do
      throwError "reconstructed preprocessing step `{input.step.name}` has the wrong result type"
    -- State the body at the decoded target, so the applied lemma below has
    -- exactly that type and needs no second check.
    pure (mkExpectedPropHint proof input.target)

/-- Introduce one fresh hypothesis for every reported parent.
The recursion is deliberately separate from the rule dispatcher: it gives all
rules the same theorem shape `parent₁ → ... → parentₙ → child`, and ensures a
handler cannot accidentally close over the concrete proof used elsewhere in
the DAG. -/
private partial def withParentHypotheses (parents : Array ParentProof) (index : Nat)
    (proofs : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  if h : index < parents.size then
    let parent := parents[index]
    let type ← inferType parent.proof
    let name := (`vampireParent).appendIndexAfter index
    withLocalDecl name .default type fun proof =>
      withParentHypotheses parents (index + 1) (proofs.push proof) k
  else
    k proofs

/-- Build a closed-over-the-parents theorem for one derived Vampire step.
For a step with parents `P₁`, ..., `Pₙ` and target `C`, the result has type
`P₁ → ... → Pₙ → C`. The local parent variables keep traces and generated
terms readable, and the theorem can be inspected independently of the proof
DAG that later applies it. -/
private def reconstructDerivedLemma (input : RuleInput) : MetaM Expr :=
  withParentHypotheses input.parents 0 #[] fun localProofs => do
    let localParents := (input.parents.zip localProofs).map fun (parent, proof) =>
      { parent with proof }
    let body ← reconstructDerivedBody { input with parents := localParents }
    mkLambdaFVars localProofs body

/-- Reconstruct one decoded Vampire step.
Input facts are checked directly. Every derived step is first proved as a
local theorem over fresh parent hypotheses and only then applied to the proofs
already stored in the DAG. This mirrors the structure of generated Lean files
from "Lean on Vampire Proofs" and keeps each inference inspectable in isolation. -/
def reconstruct (input : RuleInput) : MetaM Expr := do
  if input.sourceProof?.isSome then
    return ← reconstructSource input
  let lemma ← reconstructDerivedLemma input
  -- Printing an arbitrary proof term is counterproductive for large clause
  -- transports: a readable trace can become exponentially larger than the
  -- formula and exhaust Lean's pretty-printer stack. Rule handlers emit the
  -- useful inference-specific trace already; retain only this bounded DAG
  -- summary here.
  trace[vampire.replay] "local lemma for {input.step.name}: built over {input.parents.size} parent(s)"
  let parentProofs := input.parents.map (·.proof)
  -- Recover the conclusion while the lemma still refers to small local
  -- parent hypotheses. Inferring the type of the applied lambda instead
  -- beta-reduces it with the entire proof DAG substituted for those locals.
  -- An explicit type hint keeps later parent-type queries at this boundary;
  -- the final kernel check still checks the enclosed application.
  let mut resultType ← inferType lemma
  for parentProof in parentProofs do
    resultType ← whnf resultType
    unless resultType.isForall do
      throwError "local lemma for Vampire step `{input.step.name}` has too few parent binders"
    resultType := resultType.bindingBody!.instantiate1 parentProof
  let proof := mkExpectedPropHint (mkAppN lemma parentProofs) resultType
  -- reconstructDerivedBody already converted the lemma's conclusion to clause
  -- form, or checked and stated it at `input.target`. Repeating either after
  -- applying the parents would traverse the whole proof DAG.
  pure proof

end VampireHammer.Backend

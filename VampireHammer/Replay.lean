import VampireHammer.Replay.Decode
import VampireHammer.Replay.Import

/-!
Public replay entry point. Decoding, local reconstruction, and import are implemented by the
Replay submodules; existing imports and public names remain available.
-/

namespace VampireHammer.Replay

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal

/-- These identity theorems mark checked external reconstruction in the final
proof term. Speculative proofs discarded by tactic rollback leave no marker. -/
theorem firstOrderRefutation (proof : False) : False := proof
theorem higherOrderRefutation (proof : False) : False := proof

def markReconstruction (higherOrder : Bool) (proof : Expr) : Expr :=
  mkApp (mkConst (if higherOrder then ``higherOrderRefutation else ``firstOrderRefutation)) proof

/-- Inspect direct proof-term references, not transitive premise dependencies:
using a theorem previously proved by Vampire is still a direct Lean closure. -/
def reconstructionModes (proof : Expr) : Array String := Id.run do
  let names := proof.getUsedConstants
  let mut modes := #[]
  if names.contains ``firstOrderRefutation then modes := modes.push "fo"
  if names.contains ``higherOrderRefutation then modes := modes.push "ho"
  return modes

private def mentions (term symbol : LamTerm) : Bool :=
  term == symbol || match term with
    | .app _ fn arg => mentions fn symbol || mentions arg symbol
    | .lam _ body => mentions body symbol
    | _ => false

/-- Replay a decoded Vampire TPTP proof using the rule dispatcher in
`VampireHammer.Backend`.

Source nodes are checked against local `factN` hypotheses and do not invoke
`grind`. Unknown *derived* rules use the isolated fallback; dedicated handlers
receive their parsed metadata. The original lean-auto values are introduced
only by `importLocalProof`. -/
def replay (problem : TFF.Problem) (decoded : DecodedProof)
    (exportInhs exportFacts : Array REntry) : Auto.LamReif.ReifM Expr := do
  unless problem.facts.size == exportFacts.size do
    throwError "internal error: exported fact array does not match replay problem"
  -- Vampire has already selected its source leaves. Keep that selection in
  -- the local context and at the Lam2DAAF boundary instead of translating
  -- thousands of hypotheses that the refutation never references.
  let required := Std.HashSet.ofArray (decoded.steps.filterMap (·.sourceFact?))
  -- An input symbol recognized as a choice operator (`--choice_reasoning`)
  -- is justified by its input definition, which Vampire deletes without
  -- linking it. Keep the facts mentioning such an operator as candidates.
  let choiceOperators := decoded.steps.filterMap fun step => do
    let info ← step.inference? >>= (·.choiceAxiom?)
    guard !info.introduce
    let (_, term, _) ← problem.symbols.find? (·.1 == info.symbol)
    pure term
  let selected := (problem.facts.zip exportFacts).filter fun ((name, fact), _) =>
    required.contains name || choiceOperators.any (mentions fact ·)
  let problem := { problem with facts := selected.map (·.1) }
  let exportFacts := selected.map (·.2)
  -- Reconstruct first, before entering Lam2DAAF. The result is a closed local
  -- theorem parameterized by the TPTP sorts, symbols, and input facts.
  let tyVal ← Auto.LamReif.getTyVal
  let mut propositionAtoms : Std.HashSet Nat := {}
  let mut sortLevels : Std.HashMap Nat Level := {}
  for ((_, level), index) in tyVal.zipIdx do
    let level := (← instantiateLevelMVars level).normalize
    sortLevels := sortLevels.insert index level
    if level == .zero then
      propositionAtoms := propositionAtoms.insert index
  let localProof ← liftM <| buildLocalProof problem decoded propositionAtoms sortLevels
  let nonemptiesWithDTr ← exportInhs.mapM fun entry => do
    pure (entry, ← Auto.LamReif.collectDerivFor entry)
  let validsWithDTr ← exportFacts.mapM fun entry => do
    pure (entry, ← Auto.LamReif.collectDerivFor entry)
  let varVal ← Auto.LamReif.getVarVal
  let lamEVarTy ← Auto.LamReif.getLamEVarTy
  let result ← Auto.MetaState.runAtMetaM' <|
    (importLocalProof problem localProof nonemptiesWithDTr validsWithDTr).run'
      { tyVal, varVal, lamEVarTy }

  -- Hand the imported theorem to the same verified checker interface used by
  -- lean-auto's native backends.  The checker first supplies the Skolem terms
  -- represented by etoms, then any inhabitation witnesses used by VampLean
  -- transformations, and finally the selected source facts.
  Auto.LamReif.newAssertion result.proof (.leaf "vampire replay") result.proofLamTerm
  let etomInstantiated ← Auto.LamReif.validOfInstantiateForall
    (.valid [] result.proofLamTerm) (result.usedEtoms.map .etom)
  let forallEliminated ← Auto.LamReif.validOfElimForalls
    etomInstantiated result.usedInhs
  let contradiction ← Auto.LamReif.validOfImps
    forallEliminated result.usedHyps
  let checker ← Auto.LamReif.buildCheckerExprFor contradiction
  Meta.mkAppM ``Auto.Embedding.Lam.LamThmValid.getFalse #[checker]

end VampireHammer.Replay

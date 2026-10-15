import VampireHammer.Replay.LocalProof
import Auto.Translation.Lam2DAtomAsFVar

/-!
The single Lam2DAAF boundary: instantiate the completed local theorem and describe its premises
for lean-auto’s verified checker.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend

/-- `Lam2DAAF.withAll` exposes exported source facts as local free variables.
Recover their IDs so the final local proof can be instantiated with them. -/
private def fvarOfLemma (lemma : Auto.Lemma) : MetaM FVarId :=
  match lemma.proof with
  | .fvar fvar => pure fvar
  | _ => throwError "Vampire replay expected lean-auto to expose each input fact as a free variable"

/-- Apply the completed local theorem while checking every argument domain.

`mkAppN` only constructs syntax; it does not unify the fresh universe levels
used by the local sort variables with the levels of lean-auto's real types.
Checking each binder domain here both validates the boundary and resolves those
universe metavariables before the proof leaves `Lam2DAAF`. -/
private def applyChecked (function : Expr) (arguments : Array Expr) : MetaM (Expr × Expr) := do
  let mut application := function
  let mut type ← whnf (← inferType function)
  for (argument, index) in arguments.zipIdx do
    unless type.isForall do
      throwError "completed local Vampire proof received too many boundary arguments"
    let argumentType ← inferType argument
    unless ← isDefEq type.bindingDomain! argumentType do
      throwError "Vampire proof boundary argument {index} ({type.bindingName!}) has type\n\
        {argumentType}\nbut the completed local proof expects\n{type.bindingDomain!}"
    application := mkApp application argument
    type ← whnf (type.bindingBody!.instantiate1 argument)
  pure (application, type)

/-- What must survive the temporary lean-auto context after the completed
local proof has been imported. -/
structure ExternalReplay where
  /-- Refutation proof after temporary fvars have been abstracted as needed. -/
  proof : Expr
  /-- The first-order type of `proof`, used to register it with lean-auto's
  verified checker.  This mirrors the certificate returned by
  `Lam2DAAF.callNativeWithAtomAsFVar`. -/
  proofLamTerm : LamTerm
  /-- Existential atom IDs abstracted by the leading binders of `proof`.
  lean-auto instantiates these with the Skolem terms produced by its own
  preprocessing proof. -/
  usedEtoms : Array Nat
  /-- Inhabitation premises abstracted after the existential atoms. -/
  usedInhs : Array REntry
  /-- Exported source facts abstracted as the final implication premises. -/
  usedHyps : Array REntry

/-- Instantiate the already completed local proof with lean-auto's real sorts,
symbols, and source hypotheses.

This is the only `Lam2DAAF` boundary in replay. Individual proof steps and
unifiers never enter this context. The closed theorem is applied without eager
beta reduction, then lean-auto abstraction closes over the temporary atom and
hypothesis free variables so the proof can return to `LamReif`. -/
def importLocalProof (problem : TFF.Problem) (localProof : LocalProof)
    (nonemptiesWithDTr validsWithDTr : Array (REntry × Auto.DTr)) : Auto.Lam2DAAF.ExternM ExternalReplay :=
  Auto.MetaState.withTemporaryLCtx {} {} <| do
    let localSorts := localProof.sorts
    let localSymbolTerms := localProof.symbols
    let validsWithDTr := localProof.factIndices.map (validsWithDTr[·]!)
    let nonemptiesWithDTr := nonemptiesWithDTr.filter fun (entry, _) =>
      match entry with
      | .nonempty sort => localProof.inhabitantSorts.contains sort
      | _ => false
    trace[vampire.replay] "import completed local proof with {localSorts.size} abstract sorts, {localSymbolTerms.size} abstract symbols, {validsWithDTr.size}/{problem.facts.size} source facts"
    -- Besides the temporary Lean hypotheses, keep their `LamTerm`
    -- descriptions.  Once the temporary local context has gone away, those
    -- descriptions tell lean-auto's checker exactly what the returned Lean
    -- expression proves.
    let (inhabitantSorts, sourceTerms, lemmas, inhabitantLemmas) ←
      Auto.Lam2DAAF.withAll nonemptiesWithDTr validsWithDTr

    unless lemmas.size == localProof.factIndices.size do
      throwError "internal error: TFF fact map does not match lean-auto's preprocessed facts"
    let hypFVars ← lemmas.mapM fun lemma => Auto.MetaState.runMetaM <| fvarOfLemma lemma
    let inhabitantFVars ← inhabitantLemmas.mapM fun lemma =>
      Auto.MetaState.runMetaM <| fvarOfLemma lemma
    -- The local theorem binds only atom/etom entries.  Base `Nat` and its
    -- operations remain concrete Lean constants throughout local replay, so
    -- passing them here would give `applyChecked` extra nonexistent binders.
    let translatedSorts ← Auto.Lam2DAAF.withTranslatedLamSorts localSorts
    let translatedSymbols ← Auto.Lam2DAAF.withTranslatedLamTerms localSymbolTerms
    let atomsToAbstract ← Auto.Lam2DAAF.getAtomsToAbstract
    let etomsToAbstract ← Auto.Lam2DAAF.getEtomsToAbstract
    let lamEVarTy ← Auto.Lam2DAAF.getLamEVarTy
    let mut proof ← Auto.MetaState.runMetaM <| do
      let sourceProofs := hypFVars.map Expr.fvar
      -- `withAll` may contain witnesses for sorts absent from this particular
      -- TFF problem. Select and reorder them to match the abstract local
      -- sorts, which
      -- is also the order used by `buildLocalProof`.
      let mut localInhabitants : Array Expr := #[]
      for problemSort in localProof.inhabitantSorts do
        let some position := inhabitantSorts.findIdx? (· == problemSort)
          | throwError "lean-auto did not expose an inhabitant for exported TPTP sort {problemSort}"
        let some inhabitantFVar := inhabitantFVars[position]?
          | throwError "internal error: inhabitation proof array does not match its sorts"
        localInhabitants := localInhabitants.push (.fvar inhabitantFVar)
      let (applied, resultType) ← applyChecked localProof.proof
        (translatedSorts ++ translatedSymbols ++ localInhabitants ++ sourceProofs)
      unless ← isDefEq resultType (mkConst ``False) do
        throwError "completed local Vampire proof did not instantiate to `False`"
      -- Keep the completed theorem closed and applied. Eager beta reduction
      -- substitutes the real signature and hypotheses through the entire DAG.
      -- The domain checks above establish its type; this ordinary `id False`
      -- hint keeps later type queries small, and the kernel checks the term.
      let applied := mkExpectedPropHint applied (mkConst ``False)
      let applied ← instantiateMVars applied
      pure applied
    -- Determine every temporary fvar the proof depends on in one traversal,
    -- closed under the types of the used fvars (a source hypothesis mentions
    -- atoms, an inhabitant its sort, ...).  Abstracting fvar by fvar would
    -- traverse the whole proof once per hypothesis, etom and atom.
    let hypEntries := hypFVars.zip ((validsWithDTr.map Prod.fst).zip sourceTerms)
    let inhEntries := inhabitantFVars.zip ((nonemptiesWithDTr.map Prod.fst).zip inhabitantSorts)
    let used ← Auto.MetaState.runMetaM do
      let mut state := Lean.collectFVars {} proof
      let dependents := hypFVars.reverse ++ inhabitantFVars.reverse ++
        (etomsToAbstract.map Prod.fst).reverse ++ (atomsToAbstract.map Prod.fst).reverse
      for fvar in dependents do
        if state.fvarSet.contains fvar then
          state := Lean.collectFVars state (← instantiateMVars (← fvar.getType))
      pure state.fvarSet
    let usedHypEntries := hypEntries.filter (used.contains ·.1)
    let usedInhEntries := inhEntries.filter (used.contains ·.1)
    let usedEtomEntries := etomsToAbstract.filter (used.contains ·.1)
    let usedAtomEntries := atomsToAbstract.filter (used.contains ·.1)
    -- Binder order, outermost first: atoms (immediately applied to their
    -- original values), lean-auto etoms, inhabitation witnesses, and the
    -- source hypotheses.  The checker-side `LamTerm` below uses the same order.
    let binders : Array Expr :=
      (usedAtomEntries.map (Expr.fvar ·.1)) ++ (usedEtomEntries.map (Expr.fvar ·.1)) ++
      (usedInhEntries.map (Expr.fvar ·.1)) ++ (usedHypEntries.map (Expr.fvar ·.1))
    proof ← Auto.MetaState.runMetaM <| mkLambdaFVars binders proof
    proof := mkAppN proof (usedAtomEntries.map (·.2))
    let usedHypsWithTerms : Array (REntry × LamTerm) := usedHypEntries.map (·.2)
    let usedInhsWithSorts : Array (REntry × LamSort) := usedInhEntries.map (·.2)
    let usedEtoms := usedEtomEntries.map (·.2)

    -- Describe the type of the abstracted Lean expression in `LamTerm`.
    -- Reading from the inside out, it concludes `False`, assumes every used
    -- source formula, and quantifies over each used existential atom.  The
    -- separate outer `forall`s carry the sorts of those atoms.  This is the
    -- same encoding used by lean-auto's native backend adapter.
    let proofLamTermPre := usedHypsWithTerms.foldr
      (fun (_, sourceTerm) conclusion => sourceTerm.mkImp conclusion)
      (.base .falseE)
    let proofLamTermPre := usedInhsWithSorts.foldr
      (fun (_, sort) conclusion => conclusion.mkForallEF sort)
      proofLamTermPre
    let proofLamTermPre := proofLamTermPre.abstractsRevImp (usedEtoms.map LamTerm.etom)
    let usedEtomTys ← usedEtoms.mapM fun etom => do
      let some sort := lamEVarTy[etom]?
        | throwError "cannot recover the sort of lean-auto existential atom {etom}"
      pure sort
    let proofLamTerm := usedEtomTys.foldr
      (fun sort conclusion => LamTerm.mkForallEF sort conclusion)
      proofLamTermPre
    pure {
      proof
      proofLamTerm
      usedEtoms
      usedInhs := usedInhsWithSorts.map Prod.fst
      usedHyps := usedHypsWithTerms.map Prod.fst
    }

end VampireHammer.Replay.Internal

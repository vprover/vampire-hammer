import Lean
import VampLean

/-!
Reconstruction of Vampire's explicit Skolemization rule.

Vampire may eliminate several existential variables in one `skolemize` node.
The parent is first transformed with VampLean's `exists_prenex`; each leading
existential is then eliminated by one `Classical.choose` let binding. The
important point is that `exists_prenex` is allowed to move independent
existentials through `And`, `Or`, and universal prefixes. We recover its actual
witness order by matching variable occurrences before and after that checked
transformation, rather than predicting the simplifier's traversal order.

This module owns only the proof-producing operations. `Replay` owns the
nested local `let` declarations, because it is the only component that can
make the fresh symbols available to later proof-DAG nodes.
-/

namespace VampireHammer.BackendSkolemization

open Lean Meta Elab Tactic
open VampLean

-- Source domains can be Sort u, including propositions. VampLean's prenex
-- lemmas require Type u, which prevents lifting witnesses in those domains.
theorem orExistsPrenex {α : Sort u} [Nonempty α] (A : Prop) (B : α → Prop) :
    (A ∨ ∃ x, B x) ↔ ∃ x, A ∨ B x := by
  constructor
  · intro h
    rcases h with h | ⟨x, h⟩
    · exact ⟨Classical.choice inferInstance, Or.inl h⟩
    · exact ⟨x, Or.inr h⟩
  · rintro ⟨x, h | h⟩
    · exact Or.inl h
    · exact Or.inr ⟨x, h⟩

theorem orExistsPrenexLeft {α : Sort u} [Nonempty α] (A : Prop) (B : α → Prop) :
    ((∃ x, B x) ∨ A) ↔ ∃ x, B x ∨ A := by
  constructor
  · rintro (⟨x, h⟩ | h)
    · exact ⟨x, Or.inl h⟩
    · exact ⟨Classical.choice inferInstance, Or.inr h⟩
  · rintro ⟨x, h | h⟩
    · exact Or.inl ⟨x, h⟩
    · exact Or.inr h

theorem andExistsPrenex {α : Sort u} (A : Prop) (B : α → Prop) :
    (A ∧ ∃ x, B x) ↔ ∃ x, A ∧ B x := by
  constructor
  · rintro ⟨h, x, hx⟩; exact ⟨x, h, hx⟩
  · rintro ⟨x, h, hx⟩; exact ⟨h, x, hx⟩

theorem andExistsPrenexLeft {α : Sort u} (A : Prop) (B : α → Prop) :
    ((∃ x, B x) ∧ A) ↔ ∃ x, B x ∧ A := by
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨⟨x, hx⟩, h⟩

/-- The checked prenex proof and the original TPTP variable named by each
leading witness, in the order in which `Classical.choose` will expose it. -/
structure PrenexResult where
  proof : Expr
  variables : Array String

/-- Expose lean-auto's quantifier wrappers without unfolding proof-local
named predicates or Skolem lets. Multiple head beta steps can be necessary. -/
private partial def betaHead (e : Expr) : Expr :=
  let reduced := e.headBeta.consumeMData
  if reduced == e then e else betaHead reduced

/-- Read `Exists predicate` syntactically. Its domain is the first explicit
argument; the predicate can be a lambda or an equivalent function expression. -/
private def existential? (e : Expr) : Option (Expr × Expr) := do
  let e := betaHead e
  guard (e.isAppOfArity ``Exists 2)
  let arguments := e.getAppArgs
  pure (arguments[0]!, arguments[1]!)

/-- Mutable bookkeeping for one occurrence-matching traversal. Marker fvars
are local to the traversal; only their integer witness slots escape it. -/
private structure WitnessMatchContext where
  originalCount : Nat
  witnessSlots : Std.HashMap FVarId Nat
  nextOriginal : IO.Ref Nat
  assignments : IO.Ref (Std.HashMap Nat Nat)

/-- Walk the source and prenexed bodies in parallel, discarding original
existential wrappers and recording their witness heads at term occurrences. -/
private partial def matchWitnessBodies (context : WitnessMatchContext) (source target : Expr)
    (originals : Std.HashMap FVarId Nat) : MetaM Bool := do
  let source := betaHead source
  let target := betaHead target
  if let some (domain, predicate) := existential? source then
    let index ← context.nextOriginal.get
    if index >= context.originalCount then return false
    context.nextOriginal.set (index + 1)
    return ← withLocalDeclD `originalExistential domain fun binder =>
      matchWitnessBodies context (mkApp predicate binder) target (originals.insert binder.fvarId! index)
  if let .fvar id := source then
    if let some originalIndex := originals.get? id then
      let some witnessId := target.getAppFn.fvarId? | return false
      let some slot := context.witnessSlots.get? witnessId | return false
      let known ← context.assignments.get
      match known.get? originalIndex with
      | some previous => return previous == slot
      | none =>
        context.assignments.modify (·.insert originalIndex slot)
        return true
  match source, target with
  | .app sourceFn sourceArg, .app targetFn targetArg =>
    if !(← matchWitnessBodies context sourceFn targetFn originals) then return false
    matchWitnessBodies context sourceArg targetArg originals
  | .forallE _ sourceDomain sourceBody _, .forallE _ targetDomain targetBody _
  | .lam _ sourceDomain sourceBody _, .lam _ targetDomain targetBody _ =>
    unless ← isDefEq sourceDomain targetDomain do return false
    withLocalDeclD `prenexUniversal sourceDomain fun binder =>
      matchWitnessBodies context (sourceBody.instantiate1 binder) (targetBody.instantiate1 binder) originals
  | _, _ => isDefEq source target

/-- Match the original formula to the body of its actual prenex result.

`originalNames` lists existential binders in ordinary syntax traversal order.
Opening an original existential gives it a fresh marker fvar. An occurrence
of that marker must correspond to a leading witness of the prenexed formula,
possibly applied to universal variables after `Classical.skolem`. Its head
fvar identifies the witness slot. Universal binders are opened with the same
marker on both sides, so there is no alpha-renaming search.

The walk follows the connective and term structure without reordering it.
Repeated occurrences must identify the same witness, and the final mapping
must be a bijection. This is one structural traversal, not a search through
permutations. A vacuous original existential has no identifying occurrence;
Vampire normally eliminates these during rectification, and we decline such
an input rather than guessing its association. -/
private def matchWitnessOrder (original body : Expr) (originalNames : Array String)
    (witnesses : Array Expr) : MetaM (Option (Array String)) := do
  if witnesses.size != originalNames.size then return none
  let witnessSlots : Std.HashMap FVarId Nat :=
    (witnesses.zipIdx).foldl (fun slots (witness, index) =>
      slots.insert witness.fvarId! index) {}
  let nextOriginal ← IO.mkRef 0
  let assignments ← IO.mkRef ({} : Std.HashMap Nat Nat)
  let context : WitnessMatchContext := {
    originalCount := originalNames.size, witnessSlots, nextOriginal, assignments }
  unless ← matchWitnessBodies context original body {} do return none
  unless (← nextOriginal.get) == originalNames.size do return none
  let mut order := Array.replicate witnesses.size ""
  let assigned ← assignments.get
  for (name, index) in originalNames.zipIdx do
    let some slot := assigned.get? index | return none
    unless order[slot]!.isEmpty do return none
    order := order.set! slot name
  pure (some order)

/-- Open just the leading existential prefix of the result, retaining each
witness as a fresh fvar for `matchWitnessOrder`. The fvars remain local to this
inspection: the returned order contains only original parser names. -/
private partial def actualWitnessOrder (originalNames : Array String) (original result : Expr)
    (witnesses : Array Expr := #[]) : MetaM (Option (Array String)) := do
  if let some (domain, predicate) := existential? result then
    return ← withLocalDeclD `prenexWitness domain fun witness =>
      actualWitnessOrder originalNames original (mkApp predicate witness) (witnesses.push witness)
  matchWitnessOrder original result originalNames witnesses

/-- Apply the existential-prenex transformation used for Skolem replay.

Use VampLean's left-first lifting sequence. Witness association is recovered
from the resulting formula, so it does not depend on this priority or on the
grouping of `And`/`Or` in the decoded parent. `zetaDelta := false` keeps named
predicates folded: their definitions may contain additional existentials which
are not part of this Vampire inference. Excluding `eq_self` similarly keeps
the displayed formula structure intact. -/
def existsPrenex (parentProof : Expr) (originalNames : Array String) :
    MetaM (Option PrenexResult) := do
  let parentType ← inferType parentProof
  trace[vampire.replay] "Skolem exists_prenex input: {parentType}"
  let resultType ← mkFreshExprMVar (mkSort Level.zero)
  let theoremType := mkForall `vampireSkolemParent .default parentType resultType
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar theoremType | return none
  let tactic ← `(tactic|
    (intro vampireSkolemParent;
     repeat (first |
       simp (config := {maxSteps := 10000000, failIfUnchanged := true, zetaDelta := false}) only
         [orExistsPrenexLeft, andExistsPrenexLeft, Classical.skolem, -eq_self] at vampireSkolemParent |
       simp (config := {maxSteps := 10000000, failIfUnchanged := true, zetaDelta := false}) only
         [orExistsPrenex, andExistsPrenex, Classical.skolem, -eq_self] at vampireSkolemParent);
     exact vampireSkolemParent))
  try
    let (remaining, _) ← Lean.Elab.runTactic goal tactic
    unless remaining.isEmpty do return none
    let lemma ← instantiateMVars (.mvar goal)
    unless ← isTypeCorrect lemma do return none
    let result := mkApp lemma parentProof
    let resultType ← inferType result
    trace[vampire.replay] "Skolem exists_prenex output: {resultType}"
    let some variables ← actualWitnessOrder originalNames parentType resultType
      | do
        trace[vampire.replay] "Skolem witness-order matching failed for original binders {originalNames}"
        return none
    trace[vampire.replay] "Skolem actual witness order: {variables}"
    pure (some { proof := result, variables })
  catch error =>
    trace[vampire.replay] "Skolem exists_prenex failed: {error.toMessageData}"
    pure none

/-- Select the next existential witness from a prenexed proof.

If `proof : ∃ x : α, P x`, the result contains `Classical.choose proof : α`
and `Classical.choose_spec proof : P (Classical.choose proof)`. The caller
checks the witness type against Vampire's TFF declaration before introducing
the associated local Skolem `let`. -/
def chooseWitness (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnf (← inferType proof)
  unless type.isAppOf ``Exists do return none
  let value ← mkAppM ``Classical.choose #[proof]
  let residual ← mkAppM ``Classical.choose_spec #[proof]
  pure (some (value, residual))

/-- Match the residual proof from `exists_prenex` to Vampire's displayed
Skolemized formula. VampLean's structural `symmUnify` supplies the final
equality-orientation bridge. Calling it directly avoids running a tactic that
tries to clear the surrounding local context: the nested Skolem lets depend
on the parent proof by construction. -/
def finish (target residual : Expr) : MetaM (Option Expr) := do
  let residualType ← inferType residual
  if ← isDefEq residualType target then
    return some residual
  try
    let typeEquality ← VampLean.symmUnify residualType target
    let result ← mkAppM ``Eq.mp #[typeEquality, residual]
    unless ← isDefEq (← inferType result) target do return none
    pure (some result)
  catch _ =>
    pure none

end VampireHammer.BackendSkolemization

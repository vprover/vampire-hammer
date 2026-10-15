import VampireHammer.Backend.Common
import VampLean

/-! Direct universal-prefix movement and occurrence permutation for AVATAR.
These helpers construct ordinary theorem applications rather than running
the general prenex, simp, or AC tactics. -/

namespace VampireHammer.Backend.AvatarPrenex

open Lean Meta
open Internal VampireHammer.ClauseMeta

structure View where
  formula : Expr
  /-- Equivalence from the original formula to `formula`. -/
  equivalence : Expr

private def withFoldedLets (action : MetaM α) : MetaM α :=
  withConfig (fun config => { config with zetaDelta := false }) <|
    withFreshCache <| withReader (fun (context : Meta.Context) =>
      { context with zetaDeltaSet := {} }) action

/-- Move two independent universal blocks out of a disjunction, in left to
right order. A proposition-domain Pi is a negative literal, not a binder. -/
private partial def pull (left right : Expr) : MetaM View := do
  let left ← whnf left
  let right ← whnf right
  if let .forallE name domain body _ := left then
    unless ← isProp domain do
      return ← withLocalDeclD name domain fun value => do
        let inner ← pull (body.instantiate1 value) right
        let formula ← mkForallFVars #[value] inner.formula
        let predicate ← mkLambdaFVars #[value] (body.instantiate1 value)
        let move ← mkAppM ``VampLean.or_forall_prenex_left #[domain, right, predicate]
        let pointwise ← mkLambdaFVars #[value] inner.equivalence
        let congruence ← mkAppM ``forall_congr' #[pointwise]
        let equivalence ← mkAppM ``Iff.trans #[move, congruence]
        pure { formula, equivalence }
  if let .forallE name domain body _ := right then
    unless ← isProp domain do
      return ← withLocalDeclD name domain fun value => do
        let inner ← pull left (body.instantiate1 value)
        let formula ← mkForallFVars #[value] inner.formula
        let predicate ← mkLambdaFVars #[value] (body.instantiate1 value)
        let move ← mkAppM ``VampLean.or_forall_prenex #[left, predicate]
        let pointwise ← mkLambdaFVars #[value] inner.equivalence
        let congruence ← mkAppM ``forall_congr' #[pointwise]
        let equivalence ← mkAppM ``Iff.trans #[move, congruence]
        pure { formula, equivalence }
  let formula := mkApp2 (mkConst ``Or) left right
  let equivalence ← mkAppOptM ``Iff.rfl #[some formula]
  pure { formula, equivalence }

private partial def transformCore (formula : Expr) : MetaM View := do
  let formula ← whnf formula
  match formula with
  | .app (.app (.const ``Or _) left) right =>
    let leftView ← transformCore left
    let rightView ← transformCore right
    let merged ← pull leftView.formula rightView.formula
    let congruence ← mkAppM ``or_congr #[leftView.equivalence, rightView.equivalence]
    let equivalence ← mkAppM ``Iff.trans #[congruence, merged.equivalence]
    pure { formula := merged.formula, equivalence }
  | .forallE name domain body _ =>
    if ← isProp domain then
      let equivalence ← mkAppOptM ``Iff.rfl #[some formula]
      return { formula, equivalence }
    withLocalDeclD name domain fun value => do
      let inner ← transformCore (body.instantiate1 value)
      let formula ← mkForallFVars #[value] inner.formula
      let pointwise ← mkLambdaFVars #[value] inner.equivalence
      let equivalence ← mkAppM ``forall_congr' #[pointwise]
      pure { formula, equivalence }
  | _ => do
    let equivalence ← mkAppOptM ``Iff.rfl #[some formula]
    pure { formula, equivalence }

/-- Preserve symbolic naming predicates and carried split conditions. Only
visible first-order universal prefixes below `Or` are moved. -/
def transform (formula : Expr) : MetaM View :=
  withFoldedLets (transformCore formula)

/-- Align instantiated clauses by occurrence permutation and equality
orientation. The optimized formula/list bridges keep symbolic tree reductions
out of the matching path; the resulting proof remains kernel checked. -/
def permuteClause (proof target : Expr) : MetaM (Option Expr) :=
  withFoldedLets do
    let source ← inferType proof
    if ← isDefEq source target then return some proof
    let sourceLiterals ← flattenClause source
    let targetLiterals ← flattenClause target
    let some clause ← toClauseForm proof source 0 (some sourceLiterals) | return none
    let some aligned ← reorderAndNormalize clause sourceLiterals.toList targetLiterals.toList
      | return none
    fromClauseForm aligned target 0 (some targetLiterals)

end VampireHammer.Backend.AvatarPrenex

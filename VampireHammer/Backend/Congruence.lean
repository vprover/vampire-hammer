import VampireHammer.Backend.Common

/-! Checked congruence modulo explicitly assumed equations. Higher-order
constraints may occur beneath lambdas and proposition-valued quantifiers;
bound variables are opened as fresh locals before comparing their bodies. -/
namespace VampireHammer.Backend.Internal
open Lean Meta

partial def congruenceWithEquations (equations : Array (Expr × Expr × Expr))
    (left right : Expr) : MetaM (Option Expr) := do
  -- Substitution values are applied without normalization, so instances may
  -- contain beta-redexes; compare their reducts.
  let left := left.consumeMData.headBeta
  let right := right.consumeMData.headBeta
  unless ← isDefEq (← inferType left) (← inferType right) do return none
  if ← isDefEq left right then return some (← mkEqRefl left)
  for (proof, u, v) in equations do
    if ← (isDefEq left u <&&> isDefEq right v) then
      return ← asExpectedType proof (← mkEq left right)
    if ← (isDefEq left v <&&> isDefEq right u) then
      return ← asExpectedType (← mkEqSymm proof) (← mkEq left right)
  match left, right with
  | .app lf la, .app rf ra =>
    let some fn ← congruenceWithEquations equations lf rf | return none
    let some arg ← congruenceWithEquations equations la ra | return none
    try some <$> mkCongr fn arg catch _ => pure none
  | .lam name ld lb _, .lam _ rd rb _ =>
    unless ← isDefEq ld rd do return none
    withLocalDeclD name ld fun boundValue => do
      let some body ← congruenceWithEquations equations
          (lb.instantiate1 boundValue) (rb.instantiate1 boundValue) | return none
      let pointwise ← mkLambdaFVars #[boundValue] body
      some <$> mkAppM ``funext #[pointwise]
  | .forallE name ld lb _, .forallE _ rd rb _ =>
    unless ← (isProp left <&&> isProp right <&&> isDefEq ld rd) do return none
    withLocalDeclD name ld fun boundValue => do
      let some body ← congruenceWithEquations equations
          (lb.instantiate1 boundValue) (rb.instantiate1 boundValue) | return none
      let pointwise ← mkLambdaFVars #[boundValue] body
      let fnEquality ← mkAppM ``funext #[pointwise]
      let predicateType ← mkArrow ld (mkSort .zero)
      let quantify ← withLocalDeclD `quantifiedPredicate predicateType fun predicate => do
        let quantified ← mkForallFVars #[boundValue] (mkApp predicate boundValue)
        mkLambdaFVars #[predicate] quantified
      some <$> mkCongrArg quantify fnEquality
  | _, _ => pure none

end VampireHammer.Backend.Internal

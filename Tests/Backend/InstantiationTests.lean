import VampireHammer.Backend.Instantiation

open Lean Meta Elab Tactic
open VampireHammer.Backend
open VampireHammer.Backend.Internal

/-! Parent binder names are local to each clause, even when their sorts differ.
This is the resolution shape following functional Skolem replay: both parents
use `X0`, with substitutions `X0 ↦ a` and `X0 ↦ sk(a)` respectively. -/

private def checkParentLocalNames (left right a sk : Expr) : MetaM Unit := do
  let makeParent (name : String) (proof : Expr) : MetaM ParentProof := do
    pure {
      parent := { name }
      binders := #[{ name := "X0", sort := .base .prop }]
      existentialVariables := #[], componentBinders := #[]
      target := ← inferType proof, clauseForm := false, clauseLiterals? := none
      cnfCandidates := pure none, proof }
  let parents ← #[makeParent "left" left, makeParent "right" right].mapM id
  let input : RuleInput := {
    step := {
      name := "resolution", formula := .base .falseE, binders := #[]
      parents := parents.map (·.parent), sourceFact? := none, inference? := none
      clauseLiterals? := none }
    target := mkConst ``False, clauseLiterals? := none, parents
    sourceProof? := none, sourceFVars := #[]
    symbols := ({} : Std.HashMap String Expr).insert "a" a |>.insert "sk" sk }
  let substitutions : Array ParentSubstitution := #[
    { parent := "left", bindings := #[("X0", .atom "a")] },
    { parent := "right", bindings := #[("X0", .application "sk" #[.atom "a"])] }]
  let some instances ← instantiateParents input substitutions #[]
    | throwError "rejected differently sorted parent-local X0 binders"
  for (proof, type) in instances do
    unless ← isTypeCorrect proof do throwError "ill-typed parent instantiation"
    unless ← isDefEq (← inferType proof) type do throwError "incorrect instance type"
  -- The same spelling must not allow an ill-sorted explicit substitution.
  let wrong := substitutions.set! 1 {
    parent := "right", bindings := #[("X0", .atom "a")] }
  if (← instantiateParents input wrong #[]).isSome then
    throwError "accepted a Nat argument for a Bool binder"

example (a : Nat) (sk : Nat → Bool)
    (left : ∀ _ : Nat, True) (right : ∀ _ : Bool, True) : True := by
  run_tac withMainContext do
    let lookup (name : String) : MetaM Expr := do
      for declaration in ← getLCtx do
        if declaration.userName.toString == name then return declaration.toExpr
      throwError "missing local {name}"
    let left ← lookup "left"
    let right ← lookup "right"
    let a ← lookup "a"
    let sk ← lookup "sk"
    checkParentLocalNames left right a sk
  trivial

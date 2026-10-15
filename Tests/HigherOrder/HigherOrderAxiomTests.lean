import VampireHammer.Backend.HigherOrderAxiom

open Lean Meta Elab Tactic VampireHammer.Backend
open Auto.Embedding.Lam

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private def axiomInput (target operator : Expr) : RuleInput := {
  step := {
    name := "extensionality"
    formula := .base .trueE
    binders := #[
      { name := "F", sort := .func (.base .nat) (.base .nat) },
      { name := "G", sort := .func (.base .nat) (.base .nat) }]
    parents := #[]
    sourceFact? := none
    inference? := none
    clauseLiterals? := none }
  target
  clauseLiterals? := none
  parents := #[]
  sourceProof? := none
  sourceFVars := #[]
  symbols := ({} : Std.HashMap String Expr).insert "d" operator }

private def info : FunctionalExtensionalityInfo := {
  symbol := "d"
  leftVariable := "F"
  rightVariable := "G"
  introduce := false }

private def replayAxiom : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let input := axiomInput (← goal.getType) (← lookup "d")
  let some proof ← higherOrderFunctionalExtensionality input info
    | throwError "functional extensionality axiom declined"
  unless ← isTypeCorrect proof do throwError "ill-typed extensionality axiom"
  goal.assign proof

theorem interpreted_extensionality : ∀ f g : Nat → Nat,
    g = f ∨ g (differenceWitness f g) ≠ f (differenceWitness f g) := by
  let d : (Nat → Nat) → (Nat → Nat) → Nat := differenceWitness
  change ∀ f g : Nat → Nat, g = f ∨ g (d f g) ≠ f (d f g)
  run_tac replayAxiom

example (d : (Nat → Nat) → (Nat → Nat) → Nat) : True := by
  run_tac withMainContext do
    let d ← lookup "d"
    let functionType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
    let target ← withLocalDeclD `f functionType fun f =>
      withLocalDeclD `g functionType fun g => do
        let argument := mkApp2 d f g
        let pointwise ← mkEq (mkApp f argument) (mkApp g argument)
        let equal ← mkEq f g
        mkForallFVars #[f, g] (mkOr (mkNot pointwise) equal)
    if (← higherOrderFunctionalExtensionality (axiomInput target d) info).isSome then
      throwError "trusted an arbitrary difference operator"
  trivial

example : True := by
  let d : (Nat → Nat) → (Nat → Nat) → Nat := differenceWitness
  run_tac withMainContext do
    let d ← lookup "d"
    let functionType ← mkArrow (mkConst ``Nat) (mkConst ``Nat)
    let target ← withLocalDeclD `f functionType fun f =>
      withLocalDeclD `g functionType fun g => do
        let argument := mkApp2 d f g
        let pointwise ← mkEq (mkApp f argument) (mkApp g argument)
        let equal ← mkEq f g
        mkForallFVars #[f, g] (mkOr (mkNot pointwise) (mkNot equal))
    if (← higherOrderFunctionalExtensionality (axiomInput target d) info).isSome then
      throwError "accepted an invalid extensionality axiom"
  trivial

#print axioms interpreted_extensionality

import VampireHammer.Backend.HigherOrderChoice

open Lean Meta Elab Tactic VampireHammer.Backend

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private def choiceInput (target operator : Expr) (general : Bool) : MetaM RuleInput := do
  let symbols := ({} : Std.HashMap String Expr).insert "c" operator
  let symbols ← if general then pure symbols else pure (symbols.insert "P" (← lookup "P"))
  let domain := Auto.Embedding.Lam.LamSort.base .nat
  let names : Array FormulaBinder := if general then #[
    { name := "P", sort := .func domain (.base .prop) }, { name := "X", sort := domain }]
    else #[{ name := "X", sort := domain }]
  pure {
    step := {
      name := "choice"
      formula := .base .trueE
      binders := names
      parents := #[]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    clauseLiterals? := none
    parents := #[]
    sourceProof? := none
    sourceFVars := #[]
    symbols }

private def info (general : Bool) : ChoiceAxiomInfo := {
  symbol := "c"
  predicate := if general then .variable "P" else .atom "P"
  variableName := "X"
  introduce := false }

private def replayChoice (general : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let input ← choiceInput (← goal.getType) (← lookup "c") general
  let some proof ← higherOrderChoice input (info general) | throwError "choice axiom declined"
  unless ← isTypeCorrect proof do throwError "ill-typed choice instance"
  goal.assign proof

theorem choice_instance (P : Nat → Prop) : ∀ x,
    (P (quantifierWitness P) = True) ∨ (False = P x) := by
  let c : (Nat → Prop) → Nat := quantifierWitness
  change ∀ x, (P (c P) = True) ∨ (False = P x)
  run_tac replayChoice false

theorem choice_general : ∀ (P : Nat → Prop) x,
    (P x = False) ∨ (P (quantifierWitness P) = True) := by
  let c : (Nat → Prop) → Nat := quantifierWitness
  change ∀ (P : Nat → Prop) x, (P x = False) ∨ (P (c P) = True)
  run_tac replayChoice true

example (c : (Nat → Prop) → Nat) (P : Nat → Prop) : True := by
  run_tac withMainContext do
    let p ← lookup "P"
    let c ← lookup "c"
    let target ← withLocalDeclD `x (mkConst ``Nat) fun x => do
      let left ← mkEq (mkApp p x) (mkConst ``False)
      let right ← mkEq (mkApp p (mkApp c p)) (mkConst ``True)
      mkForallFVars #[x] (mkOr left right)
    let input ← choiceInput target c false
    if (← higherOrderChoice input (info false)).isSome then
      throwError "trusted an arbitrary function as choice"
  trivial

example (P : Nat → Prop) : True := by
  let c : (Nat → Prop) → Nat := quantifierWitness
  run_tac withMainContext do
    let p ← lookup "P"
    let c ← lookup "c"
    let target ← withLocalDeclD `x (mkConst ``Nat) fun x => do
      let left ← mkEq (mkApp p x) (mkConst ``True)
      let right ← mkEq (mkApp p (mkApp c p)) (mkConst ``False)
      mkForallFVars #[x] (mkOr left right)
    let input ← choiceInput target c false
    if (← higherOrderChoice input (info false)).isSome then
      throwError "accepted the opposite choice polarity"
  trivial

#print axioms choice_instance
#print axioms choice_general

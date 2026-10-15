import VampireHammer.Backend.HigherOrderBoolean

open Lean Meta Elab Tactic VampireHammer.Backend
open VampireHammer.Backend.Internal

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private partial def literals : Expr → Array Expr
  | .app (.app (.const ``Or _) left) right => literals left ++ literals right
  | body => #[body]

private def stripBinders (type : Expr) (count : Nat) : MetaM Expr := do
  let mut body := type
  for _ in [:count] do
    body ← whnf body
    unless body.isForall do throwError "missing clause binder"
    body := body.bindingBody!
  pure body

private def caseInput (target : Expr) (names : Array String) : MetaM RuleInput := do
  let proof ← lookup "h"
  let source ← inferType proof
  let sourceLiterals := literals (← stripBinders source names.size)
  let some stored ← toClauseForm proof source names.size (some sourceLiterals) false #[]
    | throwError "parent clause conversion failed"
  let binders := names.map fun name => { name, sort := .base .prop : FormulaBinder }
  let symbols ← if names.isEmpty then
    pure (({} : Std.HashMap String Expr).insert "p" (← lookup "p"))
    else pure {}
  pure {
    step := {
      name := "case"
      formula := .base .trueE
      binders
      parents := #[{ name := "parent" }]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    clauseLiterals? := some (literals (← stripBinders target names.size))
    parents := #[{
      parent := { name := "parent" }
      binders
      existentialVariables := #[]
      componentBinders := #[]
      target := source
      clauseForm := true
      clauseLiterals? := some sourceLiterals
      cnfCandidates := pure none
      proof := stored }]
    sourceProof? := none
    sourceFVars := #[]
    symbols }

private def certificate (names : Array String) (replaceWithTrue : Bool)
    (occurrence? : Option Nat := none) : BooleanCaseInfo := {
  literal := { parent := "parent", index := 1 }
  term := if names.isEmpty then .atom "p" else .variable "P"
  replaceWithTrue
  occurrence? }

private def replayCase (names : Array String) (replaceWithTrue : Bool)
    (occurrence? : Option Nat := none) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let input ← caseInput target names
    let some stored ← higherOrderBooleanCase input (certificate names replaceWithTrue occurrence?)
      | throwError "Boolean case declined"
    let some proof ← fromClauseForm stored target names.size input.clauseLiterals?
      | throwError "child clause conversion failed"
    unless ← isTypeCorrect proof do throwError "ill-typed Boolean case"
    goal.assign proof

theorem boolean_case_true (A p : Prop) (Q : Prop → Prop) (h : A ∨ Q p) :
    Q True ∨ p = False ∨ A := by
  run_tac replayCase #[] true

theorem boolean_case_false (A p : Prop) (Q : Prop → Prop) (h : A ∨ Q p) :
    Q False ∨ p = True ∨ A := by
  run_tac replayCase #[] false

theorem boolean_case_quantified (A : Prop) (Q : Prop → Prop) (h : ∀ p, A ∨ Q p) :
    ∀ p, Q False ∨ p = True ∨ A := by
  run_tac replayCase #["P"] false

example (A p : Prop) (Q : Prop → Prop) (h : A ∨ Q p) : True := by
  run_tac withMainContext do
    let target := mkApp (← lookup "Q") (mkConst ``True)
    let input ← caseInput target #[]
    if (← higherOrderBooleanCase input (certificate #[] true)).isSome then
      throwError "accepted missing context and truth case"
    let info := { certificate #[] true with literal := { parent := "parent", index := 9 } }
    if (← higherOrderBooleanCase input info).isSome then
      throwError "accepted invalid literal index"
  trivial

#print axioms boolean_case_true
#print axioms boolean_case_false
#print axioms boolean_case_quantified

theorem boolean_case_one_occurrence (A p : Prop) (Q : Prop → Prop → Prop) (h : A ∨ Q p p) :
    Q True p ∨ p = False ∨ A := by
  run_tac replayCase #[] true (some 0)

theorem boolean_case_second_occurrence (A p : Prop) (Q : Prop → Prop → Prop) (h : A ∨ Q p p) :
    Q p False ∨ p = True ∨ A := by
  run_tac replayCase #[] false (some 1)

#print axioms boolean_case_second_occurrence

import VampireHammer.Backend.HigherOrderQuantifier
import VampireHammer

open Lean Meta Elab Tactic VampireHammer.Backend
open VampireHammer.Backend.Internal

set_option trace.vampire.replay true

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
    unless body.isForall do throwError "missing binder"
    body := body.bindingBody!
  pure body

private def quantifierInput (target : Expr) (before after : Array String) (sigma : Bool) : MetaM RuleInput := do
  let h ← lookup "h"
  let source ← inferType h
  let sourceLiterals := literals (← stripBinders source before.size)
  let some proof ← toClauseForm h source before.size (some sourceLiterals) false #[]
    | throwError "parent conversion failed"
  let binder (name : String) : FormulaBinder := { name, sort := .base .nat }
  let symbols ← if sigma then
    pure (({} : Std.HashMap String Expr).insert "w" (← lookup "w"))
    else pure {}
  pure {
    step := {
      name := "quantifier"
      formula := .base .trueE
      binders := after.map binder
      parents := #[{ name := "parent" }]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    clauseLiterals? := some (literals (← stripBinders target after.size))
    parents := #[{
      parent := { name := "parent" }
      binders := before.map binder
      existentialVariables := #[]
      componentBinders := #[]
      target := source
      clauseForm := true
      clauseLiterals? := some sourceLiterals
      cnfCandidates := pure none
      proof }]
    sourceProof? := none
    sourceFVars := #[]
    symbols }

private def replayQuantifier (before after : Array String) (sigma : Bool) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let input ← quantifierInput target before after sigma
    let result ← if sigma then higherOrderSigma input {
      literal := { parent := "parent", index := 1 }, symbol := "w", dependencies := before }
      else higherOrderPi input
    let some stored := result | throwError "quantifier rule declined"
    let some proof ← fromClauseForm stored target after.size input.clauseLiterals?
      | throwError "child conversion failed"
    unless ← isTypeCorrect proof do throwError "ill-typed quantifier inference"
    goal.assign proof

theorem sigma_clause (A : Prop) (P : Nat → Prop) (h : A ∨ ∃ y, P y) :
    A ∨ P (quantifierWitness P) := by
  let w := quantifierWitness P
  change A ∨ P w
  run_tac replayQuantifier #[] #[] true

theorem sigma_negative_forall (A : Prop) (P : Nat → Prop) (h : A ∨ ¬∀ y, P y) :
    A ∨ ¬P (quantifierWitness (fun y => ¬P y)) := by
  let w := quantifierWitness (fun y => ¬P y)
  change A ∨ ¬P w
  run_tac replayQuantifier #[] #[] true

theorem sigma_clause_dependencies (A : Nat → Prop) (P : Nat → Nat → Prop)
    (h : ∀ x, A x ∨ ∃ y, P x y) :
    ∀ x, A x ∨ P x (quantifierWitness (P x)) := by
  let w := fun x => quantifierWitness (P x)
  change ∀ x, A x ∨ P x (w x)
  run_tac replayQuantifier #["X"] #["X"] true

theorem pi_clause (A : Prop) (P : Nat → Prop) (h : A ∨ ∀ y, P y) :
    ∀ y, P y ∨ A := by
  run_tac replayQuantifier #[] #["Y"] false

theorem pi_negative_exists (A : Prop) (P : Nat → Prop) (h : A ∨ ¬∃ y, P y) :
    ∀ y, ¬P y ∨ A := by
  run_tac replayQuantifier #[] #["Y"] false

theorem pi_clause_dependencies (A : Nat → Prop) (P : Nat → Nat → Prop)
    (h : ∀ x, A x ∨ ∀ y, P x y) : ∀ y x, P x y ∨ A x := by
  run_tac replayQuantifier #["X"] #["Y", "X"] false

example (A : Prop) (P : Nat → Prop) (h : A ∨ ∃ y, P y) : True := by
  let w := quantifierWitness P
  run_tac withMainContext do
    let target := mkApp (← lookup "P") (← lookup "w")
    let input ← quantifierInput target #[] #[] true
    if (← higherOrderSigma input {
        literal := { parent := "parent", index := 1 }, symbol := "w", dependencies := #[] }).isSome then
      throwError "dropped the clause context"
  trivial

#print axioms sigma_clause
#print axioms sigma_negative_forall
#print axioms sigma_clause_dependencies
#print axioms pi_clause_dependencies

example : True := by
  run_tac do
    let quantified ← withLocalDeclD `n (mkConst ``Nat) fun n =>
      mkForallFVars #[n] (mkConst ``False)
    if (← notArgument? quantified).isSome then
      throwError "treated a quantifier over Nat as negation"
    unless (← higherOrderLogicalLiteral quantified) == quantified do
      throwError "lost the domain of a constant quantified body"
  trivial

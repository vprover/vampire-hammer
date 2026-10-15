import VampireHammer.Backend.HigherOrder

open Lean Meta Elab Tactic
open VampireHammer.Backend VampireHammer.Backend.Internal

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private partial def literals : Expr → Array Expr
  | .app (.app (.const ``Or _) left) right => literals left ++ literals right
  | body => #[body]

private def clauseLiterals (type : Expr) (count : Nat) : MetaM (Array Expr) := do
  let mut body := type
  for _ in [:count] do
    body ← whnf body
    unless body.isForall do throwError "missing clause binder"
    body := body.bindingBody!
  pure (literals body)

private def clauseInput (proof target : Expr) (before after : Array String) : MetaM RuleInput := do
  let parentType ← inferType proof
  let source ← clauseLiterals parentType before.size
  let targetLiterals ← clauseLiterals target after.size
  let some proof ← toClauseForm proof parentType before.size (some source) false #[]
    | throwError "source clause conversion failed"
  pure {
    step := {
      name := "ho"
      formula := .base .trueE
      binders := after.map fun name => { name, sort := .base .nat }
      parents := #[{ name := "parent" }]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    clauseLiterals? := some targetLiterals
    parents := #[{
      parent := { name := "parent" }
      binders := before.map fun name => { name, sort := .base .nat }
      existentialVariables := #[]
      componentBinders := #[]
      target := parentType
      clauseForm := true
      clauseLiterals? := some source
      cnfCandidates := pure none
      proof }]
    sourceProof? := none
    sourceFVars := #[]
    symbols := {} }

private def replayEquality (rule : String) (before after : Array String) : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let input ← clauseInput (← lookup "h") target before after
    let some stored ← higherOrderEquality input rule | throwError "clause equality rule declined"
    let some proof ← fromClauseForm stored target after.size input.clauseLiterals?
      | throwError "result clause conversion failed"
    unless ← isTypeCorrect proof do throwError "invalid equality inference"
    goal.assign proof

theorem argument_congruence_clause (A : Prop) (f g : Nat → Nat) (h : A ∨ f = g) :
    ∀ x, A ∨ f x = g x := by
  run_tac replayEquality "argument_congruence" #[] #["X"]

theorem argument_congruence_curried (A : Prop) (f g : Nat → Nat → Nat) (h : f = g ∨ A) :
    ∀ x y, f x y = g x y ∨ A := by
  run_tac replayEquality "argument_congruence" #[] #["X", "Y"]

theorem positive_extensionality_clause (A : Prop) (f g : Nat → Nat)
    (h : ∀ x, A ∨ f x = g x) : A ∨ f = g := by
  run_tac replayEquality "positive_extensionality" #["X"] #[]

theorem positive_extensionality_retained_binder (A : Nat → Prop) (f g : Nat → Nat → Nat)
    (h : ∀ x y, f x y = g x y ∨ A x) : ∀ x, f x = g x ∨ A x := by
  run_tac replayEquality "positive_extensionality" #["X", "Y"] #["X"]

example (A : Nat → Prop) (f g : Nat → Nat) (h : ∀ x, A x ∨ f x = g x) : True := by
  run_tac withMainContext do
    let f ← lookup "f"
    let g ← lookup "g"
    let target ← mkEq f g
    let input ← clauseInput (← lookup "h") target #["X"] #[]
    if (← higherOrderEquality input "positive_extensionality").isSome then
      throwError "dropped a variable-dependent clause context"
  trivial

#print axioms argument_congruence_clause
#print axioms positive_extensionality_clause
#print axioms positive_extensionality_retained_binder

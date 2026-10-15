import VampireHammer.Backend_Structural

open Lean Meta Elab Tactic

/-- A carried quantified split remains an atom; only the fresh component is
expanded to recover witnesses for the principal regular clause. -/
example {α : Type} (P Q : α → Prop)
    (h : ∀ x, P x ∨ ¬ (∀ y, Q y)) :
    (∀ x, P x) ∨ ¬ (∀ y, Q y) := by
  let fresh : Prop := ∀ x, P x
  let carried : Prop := ∀ y, Q y
  have source : ∀ x, P x ∨ ¬ carried := h
  change fresh ∨ ¬ carried
  run_tac withMainContext do
    let goal ← getMainGoal
    let source := (← getLocalDeclFromUserName `source).toExpr
    let fresh := (← getLocalDeclFromUserName `fresh).toExpr
    let some proof ← VampireHammer.Structural.splitClause source (← goal.getType) (some #[fresh])
      | throwError "failed to preserve the carried quantified split"
    goal.assign proof

private def sourceClause : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.eraseMacroScopes == `source then
      return declaration.toExpr
  throwError "missing source clause"

/-! A nullary formula-naming predicate is a regular literal even when its let
value contains quantifiers. AVATAR split reconstruction may expand the split
lets in the goal, but must retain this predicate on both sides of the match.
These tests exercise that boundary without depending on Vampire's search. -/

example {α : Type} (S Q R : α → Prop)
    (h : ∀ x, (∃ y, S y) ∨ Q x ∨ R x) :
    (∃ y, S y) ∨ (∀ x, Q x ∨ R x) := by
  let named : Prop := ∃ y, S y
  let groundSplit : Prop := named
  let quantifiedSplit : Prop := ∀ x, Q x ∨ R x
  have source : ∀ x, named ∨ Q x ∨ R x := h
  change groundSplit ∨ quantifiedSplit
  run_tac withMainContext do
    let goal ← getMainGoal
    let source ← sourceClause
    let some proof ← VampireHammer.Structural.splitClause source (← goal.getType)
      | throwError "failed to retain the nullary named predicate in a positive component"
    goal.assign proof

example {α : Type} (S Q R : α → Prop)
    (h : ∀ x, ¬(∃ y, S y) ∨ Q x ∨ R x) :
    ¬(∃ y, S y) ∨ (∀ x, Q x ∨ R x) := by
  let named : Prop := ∃ y, S y
  let groundSplit : Prop := named
  let quantifiedSplit : Prop := ∀ x, Q x ∨ R x
  have source : ∀ x, ¬named ∨ Q x ∨ R x := h
  change ¬groundSplit ∨ quantifiedSplit
  run_tac withMainContext do
    let goal ← getMainGoal
    let source ← sourceClause
    let some proof ← VampireHammer.Structural.splitClause source (← goal.getType)
      | throwError "failed to retain the nullary named predicate in a negative component"
    goal.assign proof

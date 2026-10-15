import VampireHammer.Backend.Avatar

open Lean Meta Elab Tactic VampireHammer.Backend

private instance : Inhabited AvatarSplitBinding := ⟨⟨"", "", ""⟩⟩

private def component (name : String) (names : Array String) : ParentProof := {
  parent := { name }, binders := #[], existentialVariables := #[],
  componentBinders := names.map fun name => { name, sort := .base .prop },
  target := mkConst ``True, clauseForm := false, clauseLiterals? := none,
  cnfCandidates := pure none, proof := mkConst ``True.intro }

syntax "avatar_direct " str " using " term : tactic
elab_rules : tactic
  | `(tactic| avatar_direct $tag:str using $parent:term) => withMainContext do
    let source ← Term.elabTerm parent none
    let goal ← getMainGoal
    let variant := tag.getString
    let (sourceNames, parents, bindings) := match variant with
      | "reversed" =>
        (#["X0", "X1"], #[component "right" #["B"], component "left" #["A"]],
          #[ ("X0", "left", "A"), ("X1", "right", "B") ])
      | "repeated" =>
        (#["X0", "X1", "X2", "X3"], #[component "d" #["A", "B"], component "d" #["A", "B"]],
          #[ ("X0", "d", "A"), ("X1", "d", "B"), ("X2", "d", "A"), ("X3", "d", "B") ])
      | "mixed" =>
        (#["X0"], #[component "ground" #[], component "d" #["A"]], #[ ("X0", "d", "A") ])
      | "carried" =>
        (#["X0"], #[component "d" #["A"]], #[ ("X0", "d", "A") ])
      | "equality" =>
        (#["X0", "X1"], #[component "d" #["A", "B"]], #[ ("X0", "d", "A"), ("X1", "d", "B") ])
      | _ =>
        (#["X0", "X1"], #[component "left" #["A"], component "right" #["B"]],
          #[ ("X0", "left", "A"), ("X1", "right", "B") ])
    let mut bindings := bindings.map fun (sourceVariable, definitionParent, definitionVariable) =>
      ({ sourceVariable, definitionParent, definitionVariable } : AvatarSplitBinding)
    match variant with
    | "duplicate" => bindings := bindings.set! 1 bindings[0]!
    | "wrong-parent" => bindings := bindings.set! 0 { bindings[0]! with definitionParent := "absent" }
    | "wrong-binder" => bindings := bindings.set! 0 { bindings[0]! with definitionVariable := "missing" }
    | "wrong-assignment" =>
      bindings := #[{ bindings[0]! with definitionParent := "right", definitionVariable := "B" },
        { bindings[1]! with definitionParent := "left", definitionVariable := "A" }]
    | "missing" => bindings := bindings.extract 0 1
    | _ => pure ()
    let sourceBinders := sourceNames.map fun name => ({ name, sort := .base .prop } : FormulaBinder)
    let close := closeAvatarGoalDirect goal source sourceBinders parents { bindings }
    let success ← if variant == "carried" then do
      let unfoldable := (← getLCtx).foldl (init := ({} : FVarIdSet)) fun set declaration =>
        if declaration.isLet then set.insert declaration.fvarId else set
      withZetaDeltaSet unfoldable close
    else close
    unless success do
      throwError "direct AVATAR certificate rejected"
    replaceMainGoal []

example {α : Type} (P Q : α → Prop) (h : ∀ x y, P x ∨ Q y) :
    (∀ a, P a) ∨ (∀ b, Q b) := by
  avatar_direct "valid" using h

example {α β : Type} (P : α → Prop) (Q : β → Prop) (h : ∀ x y, P x ∨ Q y) :
    (∀ a, P a) ∨ (∀ b, Q b) := by
  avatar_direct "valid" using h

example {α : Type} (P Q : α → Prop) (h : ∀ x y, P x ∨ Q y) :
    (∀ b, Q b) ∨ (∀ a, P a) := by
  avatar_direct "reversed" using h

example {α : Type} (P Q : α → Prop) (R : Prop)
    (h : (∀ x y, P x ∨ Q y) ∨ R) : ((∀ a, P a) ∨ (∀ b, Q b)) ∨ R := by
  avatar_direct "valid" using h

example {α : Type} (P : α → α → Prop)
    (h : ∀ x y z w, P x y ∨ P z w) :
    (∀ a b, P a b) ∨ (∀ c d, P c d) := by
  avatar_direct "repeated" using h

example {α : Type} (P : α → Prop) (R : Prop) (h : ∀ x, ¬ R ∨ P x) :
    ¬ R ∨ (∀ a, P a) := by
  avatar_direct "mixed" using h

example {α : Type} (P Q : α → Prop) (h : ∀ x, P x ∨ (∀ y, Q y)) :
    (∀ a, P a) ∨ (∀ y, Q y) := by
  let carried : Prop := ∀ y, Q y
  have source : ∀ x, P x ∨ carried := h
  change (∀ a, P a) ∨ carried
  avatar_direct "carried" using source

example {α : Type} (Q : α → Prop) (h : ∀ x y, x = y ∨ Q y) :
    ∀ a b, Q b ∨ b = a := by
  avatar_direct "equality" using h

example {α : Type} (Q : α → Prop) (h : ∀ x y, x ≠ y ∨ Q y) :
    ∀ a b, Q b ∨ b ≠ a := by
  avatar_direct "equality" using h

example {α : Type} (P Q : α → Prop) (h : ∀ x y, P x ∨ Q y) :
    (∀ a, P a) ∨ (∀ b, Q b) := by
  fail_if_success avatar_direct "duplicate" using h
  fail_if_success avatar_direct "wrong-parent" using h
  fail_if_success avatar_direct "wrong-binder" using h
  fail_if_success avatar_direct "wrong-assignment" using h
  fail_if_success avatar_direct "missing" using h
  avatar_direct "valid" using h

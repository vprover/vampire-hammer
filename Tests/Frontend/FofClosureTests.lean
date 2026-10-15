import VampireHammer

open Lean Meta Elab Tactic VampireHammer.Backend VampireHammer.Backend.Internal
open VampireHammer.Clause

set_option trace.vampire.replay true

private def clauseShape (type : Expr) : MetaM (Array FormulaBinder × Array Expr) := do
  let mut body := type
  let mut binders := #[]
  while body.isForall do
    if ← isProp body.bindingDomain! then break
    binders := binders.push ({ name := body.bindingName!.toString, sort := .atom 0 } : FormulaBinder)
    body := body.bindingBody!
  let some view ← resolutionClauseView (mkConst ``True.intro) body
    | throwError "expected stored clause"
  pure (binders, view.regular ++ view.avatar)

syntax "replay_fof " str " using " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| replay_fof $rule:str using [$terms:term,*]) => withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let (binders, literals) ← clauseShape target
    let parents ← terms.getElems.zipIdx |>.mapM fun (term, i) => do
      let proof ← Term.elabTerm term none
      let type ← inferType proof
      let (binders, literals) ← clauseShape type
      pure ({
        parent := { name := s!"p{i}" }, binders := binders, existentialVariables := #[],
        componentBinders := #[], target := type, clauseForm := true,
        clauseLiterals? := some literals, cnfCandidates := pure none, proof := proof } : ParentProof)
    let inference : Inference := { rule := rule.getString, info := #[], parents := parents.map (·.parent) }
    let mut symbols : Std.HashMap String Expr := {}
    for decl in ← getLCtx do
      if decl.userName.toString.startsWith "spl" then symbols := symbols.insert decl.userName.toString decl.toExpr
    let input : RuleInput := {
      step := {
        name := "test", formula := .base .falseE, binders := binders,
        parents := parents.map (·.parent), sourceFact? := none,
        inference? := some inference, clauseLiterals? := some #[] },
      target := target, clauseLiterals? := some literals, parents := parents, sourceProof? := none,
      sourceFVars := #[], symbols := symbols }
    let some (_, proof) ← dispatch input inference | throwError "dedicated handler declined"
    let some proof ← toClauseForm proof target binders.size (some literals)
        (storesAClause input) (avatarAtoms input) | throwError "could not store clause result"
    let proof ← instantiateMVars proof
    if proof.hasExprMVar then throwError "unresolved reconstruction variables"
    unless ← isTypeCorrect proof do throwError "ill-typed reconstruction proof"
    unless ← isDefEq (← inferType proof) target do throwError "incorrect result"
    goal.assign proof

-- SAT closure, parent-order independence, and a proper nonempty subclause.
example (P Q : Prop) (h1 : Holds [P, Q]) (h2 : Holds [P, ¬Q])
    (h3 : Holds [¬P, Q]) (h4 : Holds [¬P, ¬Q]) : Holds [] := by
  replay_fof "global_subsumption" using [h3, h1, h4, h2]

example (P Q : Prop) (h1 : Holds [P, Q]) (h2 : Holds [P, ¬Q]) : Holds [P] := by
  replay_fof "global_subsumption" using [h2, h1]

example (P Q : Prop) (h1 : Holds [P, Q]) (valid : Holds [P]) : Holds [P] := by
  fail_if_success replay_fof "global_subsumption" using [h1]
  exact valid

-- Certificate-free binary elimination, ground and universally quantified.
example {α : Type} (a b : α) (P : α → Prop)
    (h1 : Holds [P a]) (h2 : Holds [¬P b]) : Holds [a ≠ b] := by
  replay_fof "predicate_elimination" using [h1, h2]

example {α : Type} (a : α) (P Q : α → Prop)
    (h1 : ∀ x, Holds [P x, Q x]) (h2 : Holds [¬P a]) : Holds [Q a] := by
  replay_fof "predicate_elimination" using [h1, h2]

example {α : Type} (a b : α) (P : α → Prop) (Q : α → α → Prop) (R : α → Prop)
    (h1 : ∀ x y, Holds [P x, P y, Q x y])
    (h2 : ∀ z, Holds [¬P z, R z]) : Holds [Q a b, R a, R b] := by
  replay_fof "predicate_elimination" using [h1, h2]

example {α : Type} (a b : α) (P : α → Prop)
    (h1 : Holds [P a]) (h2 : Holds [¬P b]) (valid : Holds []) : Holds [] := by
  fail_if_success replay_fof "predicate_elimination" using [h1, h2]
  exact valid

-- Independent EUF axiom checking: transitivity, nested congruence, predicates.
example {α : Type} (a b c : α) : Holds [a ≠ b, b ≠ c, a = c] := by
  replay_fof "theory_tautology_sat_conflict" using []

example {α : Type} (a b c d : α) (f : α → α → α) (g : α → α) :
    Holds [a ≠ b, c ≠ d, g (f a c) = g (f b d)] := by
  replay_fof "theory_tautology_sat_conflict" using []

example {α : Type} (a b : α) (P : α → Prop) : Holds [a ≠ b, ¬P a, P b] := by
  replay_fof "theory_tautology_sat_conflict" using []

example {α : Type} (a b : α) (valid : Holds [a = b]) : Holds [a = b] := by
  fail_if_success replay_fof "theory_tautology_sat_conflict" using []
  exact valid

-- AVATAR assumptions are carried through, not silently dropped.
example (P Q splA splB : Prop)
    (h1 : AClause.Holds [P, Q] [splA]) (h2 : AClause.Holds [P, ¬Q] [splB]) :
    AClause.Holds [P] [splA, splB] := by
  replay_fof "global_subsumption" using [h1, h2]

example {α : Type} (a b : α) (P : α → Prop) (splA splB : Prop)
    (h1 : AClause.Holds [P a] [splA]) (h2 : AClause.Holds [¬P b] [splB]) :
    AClause.Holds [a ≠ b] [splA, splB] := by
  replay_fof "predicate_elimination" using [h1, h2]

-- Global subsumption recovers alpha-renamed parent variables.
example {α : Type} (P Q : α → Prop)
    (h1 : ∀ x, Holds [P x, Q x]) (h2 : ∀ y, Holds [P y, ¬Q y]) : ∀ z, Holds [P z] := by
  replay_fof "global_subsumption" using [h2, h1]

-- Even a hypothesis retained as a let dependency cannot justify a theory axiom.
example {α : Type} (a b : α) (h : a = b) : True := by
  let picked : α := (fun (_ : a = b) => b) h
  have : Holds [picked = a] := by
    fail_if_success replay_fof "theory_tautology_sat_conflict" using []
    exact Or.inl h.symm
  trivial

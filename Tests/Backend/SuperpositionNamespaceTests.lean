import VampireHammer.Backend.Rewriting

open Lean Meta Elab Tactic VampireHammer.Backend VampireHammer.Backend.Internal
open VampireHammer.Clause

/-! Exercise the direct handler, without the dispatcher or grind fallback.
The equality parent's X0 has sort β, while the unifier RHS X0 has sort α.
This is the certificate shape of MonoidWithZeroHom.one_apply_eq_zero_iff. -/

syntax "superpose_namespace " str " using " term ", " term " with_fn " term
  " split " term : tactic

elab_rules : tactic
  | `(tactic| superpose_namespace $variant:str using $main:term, $side:term
      with_fn $fnTerm:term split $splitTerm:term) => withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let some view ← resolutionClauseView (.mvar goal) target
      | throwError "expected clause goal"
    let makeParent (name binder : String) (term : Syntax) : TacticM ParentProof := do
      let proof ← Term.elabTerm term none
      pure {
        parent := { name }, binders := #[{ name := binder, sort := .base .prop }]
        existentialVariables := #[], componentBinders := #[]
        target := ← inferType proof, clauseForm := true, clauseLiterals? := none
        cnfCandidates := pure none, proof }
    let main ← makeParent "main" "X1" main
    let side ← makeParent "side" "X0" side
    let fn ← Term.elabTerm fnTerm none
    let splitAtom ← Term.elabTerm splitTerm none
    let rhs := if variant.getString == "ill-sorted" then
      MetadataTerm.variable "X0"
    else .application "f" #[.variable "X0"]
    let substitutions : Array ParentSubstitution := #[
      { parent := "main", bindings := #[("X1", .variable "X0")] },
      { parent := "side", bindings := #[("X0", rhs)] }]
    let parents := if variant.getString == "reversed" then #[side, main] else #[main, side]
    let input : RuleInput := {
      step := {
        name := "direct", formula := .base .falseE, binders := #[]
        parents := parents.map (·.parent), sourceFact? := none, inference? := none
        clauseLiterals? := none }
      target, clauseLiterals? := some (view.regular ++ view.avatar), parents
      sourceProof? := none, sourceFVars := #[]
      symbols := ({} : Std.HashMap String Expr).insert "f" fn
        |>.insert "splTest" splitAtom }
    let some proof ← superposition input {
        substitutions, rewrittenLiteral := { parent := "main", index := 0 } }
      | throwError "direct superposition rejected the certificate"
    unless ← isTypeCorrect proof do throwError "ill-typed superposition proof"
    unless ← isDefEq (← inferType proof) target do throwError "incorrect superposition result"
    goal.assign proof

theorem replayDifferentSorts {α β : Type} (vampireInhabitant0 : α)
    (f : α → β) (c : β) (P : β → Prop) (splTest : Prop)
    (main : ∀ x, Holds [¬ P (f x)])
    (side : ∀ y, AClause.Holds [c = y] [¬ splTest]) :
    AClause.Holds [¬ P c] [¬ splTest] := by
  fail_if_success superpose_namespace "ill-sorted" using main, side with_fn f split splTest
  superpose_namespace "normal" using main, side with_fn f split splTest

theorem replayReversedParents {α β : Type} (vampireInhabitant0 : α)
    (f : α → β) (c : β) (P : β → Prop) (splTest : Prop)
    (main : ∀ x, Holds [¬ P (f x)])
    (side : ∀ y, AClause.Holds [y = c] [¬ splTest]) :
    AClause.Holds [¬ P c] [¬ splTest] := by
  superpose_namespace "reversed" using main, side with_fn f split splTest

theorem replayRejectsInvalidConclusions {α β : Type} (vampireInhabitant0 : α)
    (f : α → β) (c : β) (P : β → Prop) (splTest : Prop)
    (main : ∀ x, Holds [¬ P (f x)])
    (side : ∀ y, AClause.Holds [c = y] [¬ splTest]) :
    AClause.Holds [¬ P c] [¬ splTest] := by
  fail_if_success
    have : AClause.Holds [P c] [¬ splTest] := by
      superpose_namespace "normal" using main, side with_fn f split splTest
  fail_if_success
    have : Holds [¬ P c] := by
      superpose_namespace "normal" using main, side with_fn f split splTest
  superpose_namespace "normal" using main, side with_fn f split splTest

-- A quantified parent alone cannot supply a value of a possibly empty sort.
example (f : Empty → Bool) (c : Bool) (P : Bool → Prop) (splTest : Prop)
    (main : ∀ x, Holds [¬ P (f x)])
    (side : ∀ y, AClause.Holds [c = y] [¬ splTest]) : True := by
  fail_if_success
    have : AClause.Holds [¬ P c] [¬ splTest] := by
      superpose_namespace "normal" using main, side with_fn f split splTest
  trivial

#print axioms replayDifferentSorts
#print axioms replayReversedParents
#print axioms replayRejectsInvalidConclusions

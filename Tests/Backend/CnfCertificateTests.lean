import VampireHammer.Backend.Preprocessing

open Lean Meta Elab Tactic VampireHammer.Backend
open VampireHammer.BackendPreprocessing

syntax "convert_clause " term : tactic
elab_rules : tactic
  | `(tactic| convert_clause $parent:term) => withMainContext do
    let proof ← Term.elabTerm parent none
    let goal ← getMainGoal
    let some (_, literals) ← Internal.clauseView proof (← goal.getType)
      | throwError "expected a clause target"
    let some result ← Internal.toClauseForm proof (← inferType proof) 0 (some literals)
      | throwError "clause conversion rejected"
    goal.assign result
    replaceMainGoal []

example (P Q : Prop) (h : (P ∨ False) ∨ (P ∨ Q)) :
    VampireHammer.Clause.Holds [P, P, Q] := by
  convert_clause h

example (P Q : Prop) (h : P ∨ Q) : VampireHammer.Clause.Holds [Q, P] := by
  fail_if_success convert_clause h
  exact h.elim (fun p => Or.inr (Or.inl p)) Or.inl

example (P Q : Prop) (h : P ∨ Q) : VampireHammer.Clause.Holds [P, P, Q] := by
  fail_if_success convert_clause h
  exact h.elim Or.inl (fun q => Or.inr (Or.inr (Or.inl q)))

syntax "recover_clause " str " using " term : tactic
elab_rules : tactic
  | `(tactic| recover_clause $tag:str using $parent:term) => withMainContext do
    let proof ← Term.elabTerm parent none
    let goal ← getMainGoal
    let target ← goal.getType
    let literals ← Internal.flattenClause target
    let decoded := if tag.getString == "wrong-order" then literals.reverse else literals
    let some result ← Internal.fromClauseForm proof target 0 (some decoded)
      | throwError "reverse clause conversion rejected"
    goal.assign result
    replaceMainGoal []

example (P Q : Prop) (h : VampireHammer.Clause.Holds [P, P, Q]) :
    (P ∨ False) ∨ (P ∨ Q) := by
  recover_clause "valid" using h

example (P Q : Prop) (h : VampireHammer.Clause.Holds [P, Q]) : P ∨ Q := by
  fail_if_success recover_clause "wrong-order" using h
  recover_clause "valid" using h

syntax "cnf_certificate " str " using " term : tactic
elab_rules : tactic
  | `(tactic| cnf_certificate $variant:str using $parent:term) => withMainContext do
    let proof ← Term.elabTerm parent none
    let goal ← getMainGoal
    let tag := variant.getString
    let (parents, targets, binders) := if tag == "rename" then
      (#["X0", "X1"], #["Y1", "Y0"], #[("X0", "Y0"), ("X1", "Y1")])
      else (#[], #[], #[])
    let permutation := match tag with
      | "rename" | "reverse" | "bad-literal" => #[1, 0]
      | "duplicates" => #[0, 2, 1]
      | "swap" | "negative-swap" | "bad-swap" | "ground" => #[0]
      | "duplicate-index" => #[0, 0]
      | "out-of-range" => #[0, 2]
      | "empty" => #[]
      | _ => #[0, 1]
    let swaps := if #["swap", "negative-swap", "bad-swap"].contains tag then #[0] else #[]
    let some result ← certifiedCnf proof (← goal.getType) targets parents
        { binders, permutation, swapped := swaps }
      | throwError "CNF certificate rejected"
    goal.assign result
    replaceMainGoal []

example {α : Type} (P Q : α → Prop) (h : ∀ x y, P x ∨ Q y) :
    ∀ a b, Q a ∨ P b := by
  cnf_certificate "rename" using h

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cnf_certificate "reverse" using h

example (P Q : Prop) (h : P ∨ (P ∨ Q)) : (P ∨ Q) ∨ P := by
  cnf_certificate "duplicates" using h

example {α : Type} (x y : α) (h : x = y) : y = x := by
  cnf_certificate "swap" using h

example {α : Type} (x y : α) (h : x ≠ y) : y ≠ x := by
  cnf_certificate "negative-swap" using h

example (P : Prop) (h : P) : P := by
  cnf_certificate "ground" using h

example (h : False) : False := by
  cnf_certificate "empty" using h

example (P Q : Prop) (h : P ∨ Q) : P ∨ Q := by
  fail_if_success cnf_certificate "duplicate-index" using h
  fail_if_success cnf_certificate "out-of-range" using h
  fail_if_success cnf_certificate "bad-literal" using h
  exact h

example (P : Prop) (h : P) : P := by
  fail_if_success cnf_certificate "bad-swap" using h
  exact h

run_meta do
  let good : Inference := { rule := "cnf_transformation", parents := #[], info := #[
    .application "binder_mapping" #[.list #[]],
    .application "literal_permutation" #[.list #[.number "0"]],
    .application "swapped_equalities" #[.list #[]]] }
  unless good.cnfCertificate?.isSome do throwError "valid CNF annotation rejected"
  let duplicate := { good with info := good.info.push (.application "binder_mapping" #[.list #[]]) }
  if duplicate.cnfCertificate?.isSome then throwError "duplicate annotation accepted"
  let missing := { good with info := good.info.extract 0 2 }
  unless missing.hasCnfCertificate && missing.cnfCertificate?.isNone do
    throwError "partial annotation was not rejected"
  let malformed := { good with info := good.info.set! 1 (.application "literal_permutation" #[.list #[.number "-1"]]) }
  if malformed.cnfCertificate?.isSome then throwError "negative index accepted"

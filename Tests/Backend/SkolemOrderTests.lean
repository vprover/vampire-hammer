import VampireHammer.Backend_Skolemization

open Lean Meta Elab Tactic

/-! These checks run the real prenex transformation and recover witness names
from the resulting expression. Repeated predicate names and identical domains
are deliberate: neither types nor predicate names alone identify a witness.
The concrete COM regressions are also tested through the arena runner. -/

syntax "check_skolem_order " term " names " "[" str,* "]"
  " order " "[" str,* "]" : tactic

elab_rules : tactic
  | `(tactic| check_skolem_order $parent names [$original:str,*] order [$expected:str,*]) =>
    withMainContext do
      let parent ← Term.elabTerm parent none
      let originalNames := original.getElems.map (·.getString)
      let expected := expected.getElems.map (·.getString)
      let some result ← VampireHammer.BackendSkolemization.existsPrenex parent originalNames
        | throwError "failed to recover prenex witness order for {originalNames}"
      unless result.variables == expected do
        throwError "recovered witness order {result.variables}; expected {expected}"
      unless ← isTypeCorrect result.proof do
        throwError "prenex transformation returned an ill-typed proof"

-- Two witnesses with the same domain and the same predicate still represent
-- distinct original occurrences. Names are arbitrary, not sorted numerically.
example {α : Type} (P : α → Prop)
    (h : (∃ x, P x) ∧ (∃ y, P y)) : (∃ x, P x) ∧ (∃ y, P y) := by
  check_skolem_order h names ["X9", "X2"] order ["X9", "X2"]
  fail_if_success check_skolem_order h names ["X9"] order ["X9"]
  exact h

-- Here the actual lifting order differs from syntax order. During a right
-- lifting pass the inner `Or` exposes x, while the outer `And` lifts y first.
-- The matcher must therefore invert the two names instead of returning the
-- parser's traversal order unchanged.
example {α : Type} [Nonempty α] (P Q : α → Prop) (A : Prop)
    (h : (A ∨ ∃ x, P x) ∧ ∃ y, Q y) : (A ∨ ∃ x, P x) ∧ ∃ y, Q y := by
  check_skolem_order h names ["X0", "X1"] order ["X1", "X0"]
  exact h

-- The interleaved ground conjuncts and nested disjunctions reproduce the
-- shape of COM019+4 f121 and COM012+3 f36 without their large signatures.
example {α : Type} [Nonempty α] (P Q : α → Prop) (A B C D E : Prop)
    (h : A ∧ (B ∨ (C ∨ ∃ x, P x)) ∧ D ∧ (B ∨ (C ∨ ∃ y, Q y)) ∧ E) :
    A ∧ (B ∨ (C ∨ ∃ x, P x)) ∧ D ∧ (B ∨ (C ∨ ∃ y, Q y)) ∧ E := by
  check_skolem_order h names ["X0", "X1"] order ["X0", "X1"]
  exact h

-- Parentheses can change simp's lifting order. Check the actual result on
-- this differently grouped source, rather than relying on the TPTP fold.
example {α : Type} (P Q : α → Prop) (A B : Prop)
    (h : ((∃ x, P x) ∧ A) ∧ ((∃ y, Q y) ∧ B)) :
    ((∃ x, P x) ∧ A) ∧ ((∃ y, Q y) ∧ B) := by
  check_skolem_order h names ["left", "right"] order ["left", "right"]
  exact h

-- Nested existentials retain their associations even when their sorts differ.
example {α β : Type} (R : α → β → Prop) (h : ∃ x y, R x y) : ∃ x y, R x y := by
  check_skolem_order h names ["X8", "X3"] order ["X8", "X3"]
  exact h

-- A witness below universals becomes a function. Matching its application
-- head recovers its slot even though it is no longer a plain bound variable.
example {α β γ : Type} (R : α → β → Prop) (S : α → γ → β → Prop)
    (h : ∀ u, (∃ x, R u x) ∧ ∀ v, ∃ y, S u v y) :
    ∀ u, (∃ x, R u x) ∧ ∀ v, ∃ y, S u v y := by
  check_skolem_order h names ["X0", "X1"] order ["X0", "X1"]
  exact h

-- A named predicate can contain an existential in its let value. That binder
-- belongs to its definition, not to the current Skolem inference.
example {α : Type} (P Q : α → Prop)
    (h : (∃ z, Q z) ∧ ∃ x, P x) : (∃ z, Q z) ∧ ∃ x, P x := by
  let named : Prop := ∃ z, Q z
  have source : named ∧ ∃ x, P x := h
  check_skolem_order source names ["X0"] order ["X0"]
  exact h

-- A repeated occurrence cannot assign another witness to the same variable.
example {α : Type} (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, P x ∧ Q x := by
  check_skolem_order h names ["X0"] order ["X0"]
  exact h

-- General Sort domains occur in mathlib, including finprod_unique. Prenex
-- lifting must not constrain a source universe to be a successor.
example {α β : Sort u} [Nonempty β] (R : α → β → Prop) (A : α → Prop)
    (h : ∀ x, A x ∨ ∃ y, R x y) : ∀ x, A x ∨ ∃ y, R x y := by
  check_skolem_order h names ["X0"] order ["X0"]
  exact h

-- Include universe zero explicitly; it cannot unify with any Type universe.
example (P : Prop) [Nonempty P] (R : P → Prop) (A : Prop)
    (h : (∃ p, R p) ∨ A) : (∃ p, R p) ∨ A := by
  check_skolem_order h names ["X0"] order ["X0"]
  exact h

example {α : Sort u} (P Q : α → Prop) (A : Prop)
    (h : ((∃ x, P x) ∧ A) ∧ (A ∧ ∃ y, Q y)) :
    ((∃ x, P x) ∧ A) ∧ (A ∧ ∃ y, Q y) := by
  check_skolem_order h names ["X0", "X1"] order ["X0", "X1"]
  exact h

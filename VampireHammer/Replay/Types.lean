import VampireHammer.TFF
import VampireHammer.Backend.Types

/-!
The context-free decoded proof, typed terms, and proof-local symbol descriptions shared by
decoding and reconstruction.
-/

namespace VampireHammer.Replay

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.Backend

/-- A decoded TF0 term paired with the sort inferred from the exported
signature. TPTP applications do not annotate their intermediate result sorts,
so carrying this pair lets `apply` reject a malformed proof before it becomes a
Lean `Expr`. -/
structure TypedTerm where
  /-- The syntax tree used by lean-auto and later by `Lam2DAAF`. -/
  term : LamTerm
  /-- The term's fully checked first-order sort. -/
  sort : LamSort

/-- How a proof-local symbol obtains its Lean value. -/
inductive DerivedSymbolKind where
  /-- A witness function justified by a `skolemize` step. -/
  | skolem
  /-- A classical counterexample to a selected function disequality. -/
  | differenceWitness
  /-- Epsilon witness for a quantified HOL proxy. -/
  | quantifierWitness
  /-- A monomorphic interpreted Hilbert choice operator. -/
  | choiceOperator
  /-- Interpreted difference function for a functional extensionality axiom. -/
  | differenceOperator
  /-- A nullary proposition equated to an AVATAR component formula. -/
  | avatarDefinition
  /-- A predicate naming a subformula (`predicate_definition_introduction`). -/
  | predicateDefinition
  /-- Vampire's internal function/Boolean definition predicate, decoded as
  equality or the original predicate rather than as an abstract fresh atom. -/
  | internalDefinition
deriving Repr, BEq

/-- A symbol introduced by the proof rather than exported from lean-auto.

For introduced names, `term` is a synthetic `LamTerm.etom`; replay maps it
to a local Lean `let` and closes that let before the proof reaches `Lam2DAAF`.
Internal definition predicates instead contain their closed interpretation
(equality or the original predicate) directly. -/
structure DerivedSymbol where
  name : String
  term : LamTerm
  sort : LamSort
  kind : DerivedSymbolKind
deriving Repr

/-- Vampire's `consistent_polarity_flipping` replaces each selected predicate
`p` by `¬p` throughout the clausified problem, but keeps printing the name
`p`. It is the last preprocessing pass and the proof is printed in creation
order, so every step from the first flipping node onwards reads a flipped `p`
as `¬p`. Replay interprets that `p` as a proof-local `let` of
`fun x̄ => ¬ p x̄` from this boundary on. -/
structure PolarityFlips where
  /-- The first flipping node in file order, while its lets are pending. -/
  boundary? : Option String := none
  /-- Heads (lean-auto atoms or proof-local symbols) of the flipped predicates. -/
  heads : Array LamTerm := #[]
  /-- The introduced `let`s, kept folded like named predicates. -/
  letFVars : Array Expr := #[]
deriving Repr

/-- Context-free result of decoding a complete Vampire proof. -/
structure DecodedProof where
  steps : Array Step
  /-- Proof-local symbols, kept separate from `TFF.Problem.symbols` because
  they have no corresponding expression in the original Lean problem. -/
  derivedSymbols : Array DerivedSymbol
  polarityFlips : PolarityFlips := {}
deriving Repr

end VampireHammer.Replay

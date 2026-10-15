import VampireHammer.Replay.Types

/-!
Shared LamTerm operations used by decoding and local symbol reconstruction.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.Backend

private partial def flattenConnective (connective : LamTerm)
    (pending reversed : List LamTerm) : List LamTerm :=
  match pending with
  | [] => reversed.reverse
  | term :: rest =>
    match term with
    | .app _ (.app _ head left) right =>
      if head == connective then
        flattenConnective connective (left :: right :: rest) reversed
      else flattenConnective connective rest (term :: reversed)
    | _ => flattenConnective connective rest (term :: reversed)

/-- Flatten a disjunction so an exported source fact can be compared modulo
TPTP's associative surface syntax. Derived proof nodes deliberately do not use
this normalization: their binary grouping selects a resolution theorem.
An explicit worklist keeps long clauses linear and avoids recursive list append. -/
def flattenOr (term : LamTerm) : List LamTerm :=
  flattenConnective (.base .or) [term] []

/-- Preserve conjunct order while flattening the exporter's associative syntax. -/
def flattenAnd (term : LamTerm) : List LamTerm :=
  flattenConnective (.base .and) [term] []

/-- Domains in application order, followed by the final result sort. -/
def signature : LamSort → List LamSort × LamSort
  | .func arg result =>
    let (args, result) := signature result
    (arg :: args, result)
  | sort => ([], sort)

/-- Rebuild a nonempty connective sequence using the exporter convention.
`none` makes the impossible empty case explicit instead of manufacturing an
arbitrary formula. -/
def rightAssociate? (connective : LamTerm → LamTerm → LamTerm)
    (terms : List LamTerm) : Option LamTerm :=
  match terms.reverse with
  | [] => none
  | last :: rest => some (rest.foldl (fun tail head => connective head tail) last)

/-- Remove exactly the leading universal binders reported by TPTP. This does
not descend through arbitrary implications, which is essential because Lean
represents negation as an implication. -/
def stripLeadingForalls : Nat → LamTerm → Option LamTerm
  | 0, term => some term
  | count + 1, .app _ (.base (.forallE _)) (.lam _ body) => stripLeadingForalls count body
  | _, _ => none

end VampireHammer.Replay.Internal

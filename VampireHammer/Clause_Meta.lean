import Lean
import VampireHammer.Clause

/-!
Metaprogramming support shared by clause-oriented reconstruction rules.

`Clause.lean` intentionally contains only propositions and kernel-checked
theorems. This module is the small Lean-`Expr` layer needed to construct their
arguments from a parsed certificate. Keeping it separate prevents CNF clause
selection and explicit AC bridges from growing independent implementations of
the same occurrence-sensitive permutation algorithm.
-/

namespace VampireHammer.ClauseMeta

open Lean Meta

/-- The `List Prop` literal of `literals`: the same term as
`mkListLit (mkSort Level.zero) literals`, built without inferring the level
of `Prop` on every call. -/
def mkPropList (literals : List Expr) : Expr :=
  let prop := mkSort .zero
  literals.foldr (mkApp2 (mkApp (mkConst ``List.cons [.zero]) prop))
    (mkApp (mkConst ``List.nil [.zero]) prop)

/-- Construct a kernel `List.Perm` witness from two definitionally equal lists
of proposition expressions.

Matching consumes an occurrence from `target`, so equal duplicate literals are
kept distinct. The returned proof has type `source.Perm target` and is suitable
for the opaque `Clause.reorder` theorem. -/
partial def literalPermutation (source target : List Expr) : MetaM (Option Expr) := do
  match source, target with
  | [], [] => pure (some (← mkAppOptM ``List.Perm.nil #[some (mkSort Level.zero)]))
  | [], _ | _, [] => pure none
  | literal :: sourceTail, _ =>
    let mut position? := none
    let mut cursor := 0
    for candidate in target do
      if ← isDefEq literal candidate then
        position? := some cursor
        break
      cursor := cursor + 1
    let some position := position? | return none
    let before := target.take position
    let after := target.drop (position + 1)
    let some tailPermutation ← literalPermutation sourceTail (before ++ after)
      | return none
    let keepHead ← mkAppOptM ``List.Perm.cons
      #[some (mkSort Level.zero), some literal, none, none, some tailPermutation]
    let beforeList := mkPropList before
    let afterList := mkPropList after
    let moveHead := mkAppN (mkConst ``VampireHammer.Clause.moveToHead)
      #[beforeList, afterList, literal]
    let restoreOrder ← mkAppOptM ``List.Perm.symm
      #[some (mkSort Level.zero), none, none, some moveHead]
    some <$> mkAppOptM ``List.Perm.trans
      #[some (mkSort Level.zero), none, none, none, some keepHead, some restoreOrder]

/-- Recognize Lean's unfolded representation of a negative equality. -/
private def negatedEquality? (literal : Expr) : MetaM (Option (Expr × Expr)) := do
  let literal ← whnf literal
  unless literal.isForall do return none
  unless ← isDefEq literal.bindingBody! (mkConst ``False) do return none
  let some (_, left, right) := literal.bindingDomain!.eq? | return none
  pure (some (left, right))

/-- Produce the propositional equivalence accepted for one literal bridge.

Besides definitionally identical literals, the only normalization currently
accepted is equality symmetry, both for `a = b` and for `a ≠ b`. This
deliberately does not try arbitrary propositional simplification: a parser-side
AC bridge may reorder literals and Vampire may reverse an equality, but it
must not conceal another inference. -/
def literalEquivalent? (source target : Expr) : MetaM (Option Expr) := do
  if ← isDefEq source target then
    return some (← mkAppOptM ``Iff.rfl #[some source])
  if let some (_, sourceLeft, sourceRight) := source.eq? then
    let some (_, targetLeft, targetRight) := target.eq? | return none
    unless ← isDefEq sourceLeft targetRight do return none
    unless ← isDefEq sourceRight targetLeft do return none
    return some (← mkAppOptM ``eq_comm #[none, some sourceLeft, some sourceRight])
  -- A negative equality is represented by Lean as `(left = right) → False`.
  -- Vampire may orient the equality below that `Not` independently of the
  -- surrounding clause literal.  `ne_comm` is the exact pointwise bridge;
  -- accepting it here still cannot reorder or otherwise simplify a clause.
  let some (sourceLeft, sourceRight) ← negatedEquality? source | return none
  let some (targetLeft, targetRight) ← negatedEquality? target | return none
  unless ← isDefEq sourceLeft targetRight do return none
  unless ← isDefEq sourceRight targetLeft do return none
  some <$> mkAppOptM ``ne_comm #[none, some sourceLeft, some sourceRight]

/-- Match every target literal with one still-unused source occurrence.

The resulting source list has target order but retains the exact source
expressions.  The accompanying `↔` proofs can therefore be applied after a
real `List.Perm` proof has made the occurrence reordering visible. -/
private partial def alignLiterals (source target : List Expr) :
    MetaM (Option (List Expr × List Expr)) := do
  match target with
  | [] =>
    if source.isEmpty then pure (some ([], [])) else pure none
  | targetLiteral :: targetTail =>
    let mut found? : Option (Expr × Expr × List Expr) := none
    let mut index := 0
    for candidate in source do
      if let some equivalence ← literalEquivalent? candidate targetLiteral then
        found? := some (candidate, equivalence, source.eraseIdx index)
        break
      index := index + 1
    let some (matched, equivalence, remaining) := found? | return none
    let some (alignedTail, equivalenceTail) ← alignLiterals remaining targetTail
      | return none
    pure (some (matched :: alignedTail, equivalence :: equivalenceTail))

/-- Build `Clause.Equivalent` from the pointwise literal equivalences found by
`alignLiterals`.  It is kept here because the values are Lean expressions
decoded from the TPTP proof, while the inductive relation itself belongs to
the trusted logical interface in `Clause.lean`. -/
private partial def equivalentWitness (source target equivalences : List Expr) :
    MetaM (Option Expr) := do
  match source, target, equivalences with
  | [], [], [] => return some (mkConst ``VampireHammer.Clause.Equivalent.nil)
  | _ :: sourceTail, _ :: targetTail, equivalence :: equivalenceTail =>
    let some tail ← equivalentWitness sourceTail targetTail equivalenceTail | return none
    some <$> mkAppM ``VampireHammer.Clause.Equivalent.cons
      #[equivalence, tail]
  | _, _, _ => pure none

/-- Whether every pointwise literal equivalence is reflexive. -/
private def allReflexive (equivalences : List Expr) : Bool :=
  equivalences.all (·.isAppOf ``Iff.rfl)

/-- State `proof` at the clause type `Clause.Holds target`.  Used when `target`
is definitionally the proof's own literal list, where a `Clause.map` over a
chain of `Iff.rfl` would only enlarge the proof term. -/
private def atClause (proof : Expr) (target : List Expr) : MetaM Expr := do
  let targetList := mkPropList target
  mkExpectedTypeHint proof (mkApp (mkConst ``VampireHammer.Clause.Holds) targetList)

/-- Transport a clause proof across pointwise equality-orientation changes
without permitting a literal permutation.

This is the local bridge used after superposition and demodulation. Their
logical rule fixes the occurrence order, but Vampire may print an equality
literal as `b = a` when the natural rewritten literal is `a = b`, including
below a negation. -/
def normalizeEqualityOrientations (sourceProof : Expr) (source target : List Expr) :
    MetaM (Option Expr) := do
  if source.length != target.length then return none
  let mut pointwise := #[]
  for (sourceLiteral, targetLiteral) in source.zip target do
    let some equivalence ← literalEquivalent? sourceLiteral targetLiteral | return none
    pointwise := pointwise.push equivalence
  let equivalences := pointwise.toList
  if allReflexive equivalences then return some (← atClause sourceProof target)
  let some equivalent ← equivalentWitness source target equivalences | return none
  some <$> mkAppM ``VampireHammer.Clause.map #[equivalent, sourceProof]

/-- Change one selected clause literal to a definitionally equal or
equality-symmetric spelling.

The returned list has exactly the same length and occurrence order as
`source`; only `index` is replaced.  `normalizeEqualityOrientations` supplies
the kernel-checked `Clause.map` bridge, so this accepts precisely reflexive
spelling changes, `a = b`/`b = a`, and `a ≠ b`/`b ≠ a`.  Calculus handlers use
this before inspecting selected literals, which keeps orientation handling out
of their inference-specific proof construction. -/
def orientLiteralAt (sourceProof : Expr) (source : List Expr) (index : Nat)
    (targetLiteral : Expr) : MetaM (Option (Expr × List Expr)) := do
  unless index < source.length do return none
  let target := source.set index targetLiteral
  let some proof ← normalizeEqualityOrientations sourceProof source target | return none
  pure (some (proof, target))

/-- Convert a clause proof to another literal spelling by an explicit
occurrence permutation followed by pointwise literal equivalences.

This is used for the synthetic parser AC nodes and for VampLean CNF selection.
It accepts equality symmetry in addition to a pure permutation, but retains
both operations as named theorem applications in the generated proof term. -/
def reorderAndNormalize (sourceProof : Expr) (source target : List Expr) :
    MetaM (Option Expr) := do
  let some (alignedSource, equivalences) ← alignLiterals source target | return none
  -- `alignLiterals` keeps the exact source expressions, so an unchanged order
  -- is recognized syntactically and needs no permutation proof.
  let reordered ← if alignedSource == source then pure sourceProof else
    let some permutation ← literalPermutation source alignedSource | return none
    mkAppOptM ``VampireHammer.Clause.reorder
      #[none, none, some permutation, some sourceProof]
  if allReflexive equivalences then return some (← atClause reordered target)
  let some equivalent ← equivalentWitness alignedSource target equivalences | return none
  some <$> mkAppM ``VampireHammer.Clause.map #[equivalent, reordered]

/-- Construct a proof that one concrete literal occurs in a concrete target
list.  The first definitionally equal occurrence is used; unlike permutation
construction, this occurrence is not consumed because subsumption uses
set-like containment rather than multiset containment. -/
private partial def literalMembership (literal : Expr) :
    List Expr → MetaM (Option Expr)
  | [] => pure none
  | head :: tail => do
    if ← isDefEq literal head then
      let tailList := mkPropList tail
      return some (← mkAppOptM ``List.Mem.head
        #[some (mkSort Level.zero), some literal, some tailList])
    let some tailProof ← literalMembership literal tail | return none
    let tailList := mkPropList tail
    some <$> mkAppOptM ``List.Mem.tail
      #[some (mkSort Level.zero), some literal, some head, some tailList, some tailProof]

/-- Build the explicit `Clause.Contained target source` certificate used by
forward subsumption resolution.  Every source literal must be definitionally
equal to some target literal; duplicate source occurrences may reuse a target
occurrence because clause truth is idempotent. -/
partial def containedWitness (source target : List Expr) : MetaM (Option Expr) := do
  let targetList := mkPropList target
  match source with
  | [] => some <$> mkAppOptM ``VampireHammer.Clause.Contained.nil #[some targetList]
  | literal :: rest =>
    let some member ← literalMembership literal target | return none
    let some tail ← containedWitness rest target | return none
    let restList := mkPropList rest
    some <$> mkAppOptM ``VampireHammer.Clause.Contained.cons
      #[some targetList, some literal, some restList, some member, some tail]

end VampireHammer.ClauseMeta

/-!
The small logical interface used by clause inferences.

TPTP writes a clause with `|`, but the nesting of Lean's binary `Or` is an
implementation detail of the parser. A resolution certificate instead talks
about an ordered collection of literal occurrences and their positions.
`Holds` is the bridge: it gives an ordered list its usual disjunctive meaning,
without assigning significance to an `Or` tree's parentheses.

Lists, rather than sets, are deliberate. Clauses may contain duplicate
literals, and Vampire's literal indices refer to occurrences. The list order
also lets reconstruction retain the order recorded in the certificate.
-/

namespace VampireHammer.Clause

/-- The proposition expressed by an ordered clause. The empty clause is false. -/
def Holds (literals : List Prop) : Prop := literals.foldr Or False

/-- A signed propositional atom at the AVATAR-to-Boolean boundary. -/
structure SignedLiteral where
  atom : Prop
  positive : Bool

def SignedLiteral.proposition (literal : SignedLiteral) : Prop :=
  if literal.positive then literal.atom else ¬ literal.atom

/-- The Boolean value of a signed atom. -/
noncomputable def SignedLiteral.boolean (literal : SignedLiteral) : Bool :=
  if literal.positive then @decide literal.atom (Classical.propDecidable literal.atom)
  else !(@decide literal.atom (Classical.propDecidable literal.atom))

noncomputable def SignedLiteral.clause (literals : List SignedLiteral) : Bool :=
  (literals.map SignedLiteral.boolean).foldr Bool.or false

/-- One opaque bridge per clause, independent of its size and literal signs.
The recursive conversion is proved once here rather than generated during
every SAT refutation. -/
theorem SignedLiteral.toBoolean (literals : List SignedLiteral) :
    Holds (literals.map SignedLiteral.proposition) →
      SignedLiteral.clause literals = true := by
  classical
  induction literals with
  | nil => exact False.elim
  | cons literal literals ih =>
    intro clause
    rcases clause with head | tail
    · apply (Bool.or_eq_true _ _).mpr
      apply Or.inl
      cases literal with
      | mk atom positive =>
        cases positive <;>
          simpa only [SignedLiteral.proposition, SignedLiteral.boolean,
            Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq,
            Bool.not_eq_true', decide_eq_false_iff_not] using head
    · exact (Bool.or_eq_true _ _).mpr (Or.inr (ih tail))

/-- A compact certificate that all literals of a clause are false. -/
inductive AllFalse : List Prop → Prop where
  | nil : AllFalse []
  | cons (literal : Prop) (tail : List Prop) :
      (¬ literal) → AllFalse tail → AllFalse (literal :: tail)

theorem AllFalse.notHolds : ∀ {literals : List Prop}, AllFalse literals → ¬ Holds literals
  | [], .nil => id
  | _ :: _, .cons _ _ head tail => fun clause =>
      Or.elim clause head (AllFalse.notHolds tail)

/-- Unit propagation retains the only literal not already known to be false. -/
theorem unitOfFalse (before after : List Prop) (literal : Prop) :
    AllFalse before → AllFalse after → Holds (before ++ literal :: after) → literal := by
  induction before with
  | nil =>
    intro _ rest clause
    exact Or.elim clause id (fun tail => False.elim (AllFalse.notHolds rest tail))
  | cons head before ih =>
    intro first rest clause
    cases first with
    | cons _ _ notHead tail =>
      exact Or.elim clause (fun h => False.elim (notHead h)) (ih tail rest)

theorem notHeadOfNotHolds (literal : Prop) (tail : List Prop) :
    (¬ Holds (literal :: tail)) → ¬ literal := fun h head => h (Or.inl head)

theorem notTailOfNotHolds (literal : Prop) (tail : List Prop) :
    (¬ Holds (literal :: tail)) → ¬ Holds tail := fun h rest => h (Or.inr rest)

/-- Embed the left clause into an appended clause. -/
theorem appendLeft : ∀ (left right : List Prop), Holds left → Holds (left ++ right)
  | [], _, proof => False.elim proof
  | _ :: left, right, proof =>
    Or.elim proof Or.inl (fun tail => Or.inr (appendLeft left right tail))

/-- Embed the right clause into an appended clause. -/
theorem appendRight : ∀ (left right : List Prop), Holds right → Holds (left ++ right)
  | [], _, proof => proof
  | _ :: left, right, proof => Or.inr (appendRight left right proof)

/-! ## The parser-facing clause tree

`Holds` is the representation used by inference theorems. The parser,
however, gives the backend an arbitrarily-associated binary `Or` tree. `Tree`
records that tree explicitly while retaining its propositions at the leaves.
The two conversion theorems below are deliberately named, opaque theorem calls:
replayed proof terms should show a clause conversion, rather than its internal
sequence of `Or.elim`, `Or.inl`, and `Or.inr` applications.
-/

/-- A binary disjunction tree as it appeared in the parsed TPTP formula. -/
inductive Tree where
  /-- The empty clause. -/
  | empty
  /-- A one-literal clause. -/
  | atom (proposition : Prop)
  /-- The parser's binary disjunction node. -/
  | join (left right : Tree)

/-- Read a parser-shaped clause tree as a Lean proposition. -/
def Tree.denote : Tree → Prop
  | .empty => False
  | .atom proposition => proposition
  | .join left right => left.denote ∨ right.denote

/-- Read the leaves of a parser-shaped clause tree from left to right. -/
def Tree.literals : Tree → List Prop
  | .empty => []
  | .atom proposition => [proposition]
  | .join left right => left.literals ++ right.literals

/-- A disjunction of two appended clause lists has a proof from one side. -/
private theorem splitAppend : ∀ (left right : List Prop),
    Holds (left ++ right) → Holds left ∨ Holds right
  | [], _, proof => Or.inr proof
  | _ :: left, right, proof =>
    Or.elim proof
      (fun literalProof => Or.inl (Or.inl literalProof))
      (fun tailProof => Or.elim (splitAppend left right tailProof)
        (fun leftProof => Or.inl (Or.inr leftProof))
        Or.inr)

/-- Convert a parsed binary `Or` tree to its ordered list-clause meaning. -/
theorem Tree.toHolds : ∀ (tree : Tree), tree.denote → Holds tree.literals
  | .empty, proof => proof
  | .atom _, proof => Or.inl proof
  | .join left right, proof =>
    Or.elim proof
      (fun leftProof => appendLeft left.literals right.literals (toHolds left leftProof))
      (fun rightProof => appendRight left.literals right.literals (toHolds right rightProof))

/-- Convert an ordered list-clause proof back to the parser's original binary
`Or` tree. Together with `Tree.toHolds`, this confines association conversion
to two readable theorem applications in generated proof terms. -/
theorem Tree.fromHolds : ∀ (tree : Tree), Holds tree.literals → tree.denote
  | .empty, proof => proof
  | .atom _, proof => Or.elim proof id False.elim
  | .join left right, proof =>
    Or.elim (splitAppend left.literals right.literals proof)
      (fun leftProof => Or.inl (fromHolds left leftProof))
      (fun rightProof => Or.inr (fromHolds right rightProof))

/-- A clause remains true when its literals are permuted. -/
theorem perm {left right : List Prop} : left.Perm right → Holds left → Holds right
  | .nil, proof => proof
  | .cons _ permutation, proof =>
    Or.elim proof Or.inl (fun tail => Or.inr (perm permutation tail))
  | .swap _ _ _, proof =>
    Or.elim proof
      (fun second => Or.inr (Or.inl second))
      (fun rest => Or.elim rest Or.inl (fun tail => Or.inr (Or.inr tail)))
  | .trans first second, proof => perm second (perm first proof)

/-- A position-by-position logical equivalence between two clause lists.

`List.Perm` is the right certificate when the literal propositions themselves
are unchanged.  TPTP, however, also permits a prover to print an equality in
the opposite orientation while preserving the same clause.  This small
relation records the corresponding `↔` proof at each position after any
literal reordering has already been made explicit. -/
inductive Equivalent : List Prop → List Prop → Prop where
  | nil : Equivalent [] []
  | cons {source target : Prop} {sources targets : List Prop} :
      (source ↔ target) → Equivalent sources targets →
      Equivalent (source :: sources) (target :: targets)

/-- Transport a true clause across position-by-position equivalent literals.

The separate `reorder` theorem remains responsible for changes of occurrence
order.  Keeping this transport independent makes a proof term show both
steps: first its order changes, then any equality literals are normalized. -/
theorem map : ∀ {source target : List Prop}, Equivalent source target →
    Holds source → Holds target
  | [], [], .nil, proof => proof
  | _ :: _, _ :: _, .cons equivalent rest, proof =>
    Or.elim proof
      (fun sourceProof => Or.inl (equivalent.mp sourceProof))
      (fun sourceProof => Or.inr (map rest sourceProof))

/-- Move one literal from its reported position to the front of a list.
The `before` list is exactly the zero-based position supplied by Vampire. -/
theorem moveToHead (before after : List Prop) (literal : Prop) :
    (before ++ literal :: after).Perm (literal :: before ++ after) := by
  induction before with
  | nil => exact .refl _
  | cons first before induction =>
    exact .trans (.cons first induction) (.swap literal first (before ++ after))

/-- Soundness of binary resolution for arbitrary reported literal positions.

`positiveBefore.length` and `negativeBefore.length` are the two resolved
literal indices. The result preserves each parent's original order with that
one occurrence removed: `positiveBefore ++ positiveAfter`, followed by the
corresponding negative tail. -/
theorem resolve (literal : Prop)
    (positiveBefore positiveAfter negativeBefore negativeAfter : List Prop) :
    Holds (positiveBefore ++ literal :: positiveAfter) →
      Holds (negativeBefore ++ (¬ literal) :: negativeAfter) →
        Holds ((positiveBefore ++ positiveAfter) ++ (negativeBefore ++ negativeAfter)) := by
  intro positive negative
  have positiveHead : Holds (literal :: (positiveBefore ++ positiveAfter)) :=
    perm (moveToHead positiveBefore positiveAfter literal) positive
  have negativeHead : Holds ((¬ literal) :: (negativeBefore ++ negativeAfter)) :=
    perm (moveToHead negativeBefore negativeAfter (¬ literal)) negative
  exact Or.elim positiveHead
    (fun value => Or.elim negativeHead
      (fun notLiteral => False.elim (notLiteral value))
      (appendRight (positiveBefore ++ positiveAfter) _))
    (appendLeft _ (negativeBefore ++ negativeAfter))

/-- Soundness of binary resolution when Vampire reports the negative parent
first.

This is the parent-order companion of `resolve`.  It deliberately keeps the
tail of the negative parent before the tail of the positive parent, matching
the order in Vampire's proof DAG.  The backend selects this theorem from the
polarity of the two named resolved occurrences; it therefore does not need to
swap proof parents or insert a clause permutation merely to fit one theorem's
argument order. -/
theorem resolveNegatedFirst (literal : Prop)
    (negativeBefore negativeAfter positiveBefore positiveAfter : List Prop) :
    Holds (negativeBefore ++ (¬ literal) :: negativeAfter) →
      Holds (positiveBefore ++ literal :: positiveAfter) →
        Holds ((negativeBefore ++ negativeAfter) ++ (positiveBefore ++ positiveAfter)) := by
  intro negative positive
  have negativeHead : Holds ((¬ literal) :: (negativeBefore ++ negativeAfter)) :=
    perm (moveToHead negativeBefore negativeAfter (¬ literal)) negative
  have positiveHead : Holds (literal :: (positiveBefore ++ positiveAfter)) :=
    perm (moveToHead positiveBefore positiveAfter literal) positive
  exact Or.elim negativeHead
    (fun notLiteral => Or.elim positiveHead
      (fun value => False.elim (notLiteral value))
      (appendRight (negativeBefore ++ negativeAfter) _))
    (appendLeft _ (positiveBefore ++ positiveAfter))

/-- Soundness of constrained resolution (resolution with unification with
abstraction).

The selected occurrences `first` and `second` need to be complementary only
when no constraint holds, i.e. when every abstracted disequality is in fact an
equality. As in Vampire's result, the constraints precede the two parent
tails. Both polarity orders are covered because `complementary` is symmetric
in shape. -/
theorem constrainedResolve (first second : Prop) (constraints : List Prop)
    (firstBefore firstAfter secondBefore secondAfter : List Prop)
    (complementary : ¬ Holds constraints → first → second → False) :
    Holds (firstBefore ++ first :: firstAfter) →
      Holds (secondBefore ++ second :: secondAfter) →
        Holds (constraints ++ ((firstBefore ++ firstAfter) ++ (secondBefore ++ secondAfter))) := by
  intro firstClause secondClause
  by_cases constraint : Holds constraints
  · exact appendLeft _ _ constraint
  · apply appendRight
    have firstHead : Holds (first :: (firstBefore ++ firstAfter)) :=
      perm (moveToHead firstBefore firstAfter first) firstClause
    have secondHead : Holds (second :: (secondBefore ++ secondAfter)) :=
      perm (moveToHead secondBefore secondAfter second) secondClause
    exact Or.elim firstHead
      (fun firstValue => Or.elim secondHead
        (fun secondValue => False.elim (complementary constraint firstValue secondValue))
        (appendRight (firstBefore ++ firstAfter) _))
      (appendLeft _ (secondBefore ++ secondAfter))

/-! ## AVATAR bookkeeping

These lemmas keep AVATAR's elementary propositional steps visible as named
operations on `Clause.Holds`. In particular, `component` may itself be a
quantified proposition; it remains one literal and no binder is moved across
the surrounding clause.
-/

/-- From the local definition `split ↔ component`, derive Vampire's component
clause `component ∨ ¬split`.

The premise is a singleton clause because every post-CNF proof node is stored
uniformly as `Clause.Holds`, including AVATAR definition nodes. -/
opaque avatarComponentClause (split component : Prop) :
    Holds [split ↔ component] → Holds [component, ¬split] := by
  intro definition
  rcases definition with definition | impossible
  · by_cases splitProof : split
    · exact Or.inl (definition.mp splitProof)
    · exact Or.inr (Or.inl splitProof)
  · exact False.elim impossible

/-- Remove the explicit `$false` disjunct from an AVATAR contradiction clause.
The TPTP decoder already represents `$false` as no literal, so this is the
identity at the list-clause boundary. -/
opaque avatarContradictionClause (remaining : List Prop) :
    Holds remaining → Holds remaining := by
  intro proof
  exact proof

/-! ## AVATAR A-clauses

Vampire's A-clauses have two logically distinct clause parts: an ordered list
of first-order literals and a *set-like* collection of propositional AVATAR
literals. `List Prop` remains the concrete carrier for the AVATAR part: that
keeps parsing and proof-term printing simple, and does not require decidable
equality on propositions. Its semantic interface is nevertheless extensional:
two AVATAR lists with the same members (irrespective of order or duplicates)
are interchangeable. Any first-order variables are quantified around the
complete A-clause. A later first-order inference changes only the regular
clause; the AVATAR context is carried through as a set.
-/

namespace AClause

/-- The meaning of an A-clause with an ordered regular clause and set-like
AVATAR context.

`firstOrderLiterals` is an ordinary first-order clause, not one opaque
formula. Keeping it as a list preserves Vampire's literal indices and lets the
existing resolution/superposition lemmas operate on that side. The second
list contains only propositional AVATAR literals; `transportAvatarSet` below
makes its order and multiplicity semantically irrelevant. -/
def Holds (firstOrderLiterals avatarLiterals : List Prop) : Prop :=
  Clause.Holds firstOrderLiterals ∨ Clause.Holds avatarLiterals

/-- Split an appended ordinary clause at the first-order/AVATAR boundary. -/
private theorem splitAppend : ∀ (firstOrder avatar : List Prop),
    Clause.Holds (firstOrder ++ avatar) →
      Clause.Holds firstOrder ∨ Clause.Holds avatar
  | [], _, proof => Or.inr proof
  | _ :: firstOrder, avatar, proof =>
    Or.elim proof
      (fun literalProof => Or.inl (Or.inl literalProof))
      (fun tailProof => Or.elim (splitAppend firstOrder avatar tailProof)
        (fun firstOrderProof => Or.inl (Or.inr firstOrderProof))
        Or.inr)

/-- Enter A-clause form after the decoder has separated the two literal lists. -/
opaque fromClause (firstOrder avatar : List Prop) :
    Clause.Holds (firstOrder ++ avatar) →
      Holds firstOrder avatar := by
  intro proof
  exact splitAppend firstOrder avatar proof

/-- Return to the ordinary concatenated clause view at an explicit boundary. -/
opaque toClause (firstOrder avatar : List Prop) :
    Holds firstOrder avatar →
      Clause.Holds (firstOrder ++ avatar) := by
  intro proof
  exact Or.elim proof
    (Clause.appendLeft firstOrder avatar)
    (Clause.appendRight firstOrder avatar)

/-- Apply an inference to the regular clause while carrying every AVATAR
literal through unchanged. This is the central reconstruction rule for
A-clauses. -/
opaque mapFirstOrder (source target avatar : List Prop) :
    (Clause.Holds source → Clause.Holds target) →
      Holds source avatar → Holds target avatar := by
  intro transform clause
  exact Or.elim clause
    (fun sourceProof => Or.inl (transform sourceProof))
    Or.inr

/-- Apply independently checked bridges to both halves of an A-clause. This
is used only by an explicit AC proof node. The regular bridge preserves its
occurrence-sensitive ordering; the AVATAR bridge may use its set semantics. -/
opaque mapParts (sourceRegular targetRegular sourceAvatar targetAvatar : List Prop) :
    (Clause.Holds sourceRegular → Clause.Holds targetRegular) →
      (Clause.Holds sourceAvatar → Clause.Holds targetAvatar) →
        Holds sourceRegular sourceAvatar → Holds targetRegular targetAvatar := by
  intro regularTransform avatarTransform clause
  exact Or.elim clause
    (fun regularProof => Or.inl (regularTransform regularProof))
    (fun avatarProof => Or.inr (avatarTransform avatarProof))

/-- Regard an ordinary first-order clause as an A-clause with no AVATAR
literals. This lets one theorem cover resolution between an A-clause and an
ordinary clause. -/
opaque ofFirstOrder (firstOrder : List Prop) :
    Clause.Holds firstOrder → Holds firstOrder [] := by
  exact Or.inl

/-- Binary resolution on the regular halves of two A-clauses.

The selected occurrences and all four regular tails have exactly the same
meaning as in `Clause.resolve`. The AVATAR lists are never inspected or
rewritten: when one of them already proves its parent A-clause, it is copied
to the result. When both parents are A-clauses their AVATAR lists are appended
in parent order. -/
opaque resolve (literal : Prop)
    (positiveBefore positiveAfter negativeBefore negativeAfter : List Prop)
    (positiveAvatar negativeAvatar : List Prop) :
    Holds (positiveBefore ++ literal :: positiveAfter) positiveAvatar →
      Holds (negativeBefore ++ (¬ literal) :: negativeAfter) negativeAvatar →
        Holds
          ((positiveBefore ++ positiveAfter) ++ (negativeBefore ++ negativeAfter))
          (positiveAvatar ++ negativeAvatar) := by
  intro positiveClause negativeClause
  exact Or.elim positiveClause
    (fun positiveRegular => Or.elim negativeClause
      (fun negativeRegular => Or.inl
        (Clause.resolve literal positiveBefore positiveAfter negativeBefore negativeAfter
          positiveRegular negativeRegular))
      (fun negativeAvatarProof => Or.inr
        (Clause.appendRight positiveAvatar negativeAvatar negativeAvatarProof)))
    (fun positiveAvatarProof => Or.inr
      (Clause.appendLeft positiveAvatar negativeAvatar positiveAvatarProof))

/-- A-clause counterpart of `Clause.constrainedResolve`. The constraints
precede the two regular tails; the AVATAR lists are appended in parent order,
exactly as for `resolve`. -/
opaque constrainedResolve (first second : Prop) (constraints : List Prop)
    (firstBefore firstAfter secondBefore secondAfter : List Prop)
    (firstAvatar secondAvatar : List Prop)
    (complementary : ¬ Clause.Holds constraints → first → second → False) :
    Holds (firstBefore ++ first :: firstAfter) firstAvatar →
      Holds (secondBefore ++ second :: secondAfter) secondAvatar →
        Holds
          (constraints ++ ((firstBefore ++ firstAfter) ++ (secondBefore ++ secondAfter)))
          (firstAvatar ++ secondAvatar) := by
  intro firstClause secondClause
  exact Or.elim firstClause
    (fun firstRegular => Or.elim secondClause
      (fun secondRegular => Or.inl
        (Clause.constrainedResolve first second constraints firstBefore firstAfter
          secondBefore secondAfter complementary firstRegular secondRegular))
      (fun secondAvatarProof => Or.inr
        (Clause.appendRight firstAvatar secondAvatar secondAvatarProof)))
    (fun firstAvatarProof => Or.inr
      (Clause.appendLeft firstAvatar secondAvatar firstAvatarProof))

/-- A-clause counterpart of `Clause.resolveNegatedFirst`.

The regular tail order and the AVATAR-context order both follow Vampire's
parent order: negative parent first, then positive parent.  AVATAR literals
remain alternatives and are never inspected by the first-order inference. -/
opaque resolveNegatedFirst (literal : Prop)
    (negativeBefore negativeAfter positiveBefore positiveAfter : List Prop)
    (negativeAvatar positiveAvatar : List Prop) :
    Holds (negativeBefore ++ (¬ literal) :: negativeAfter) negativeAvatar →
      Holds (positiveBefore ++ literal :: positiveAfter) positiveAvatar →
        Holds
          ((negativeBefore ++ negativeAfter) ++ (positiveBefore ++ positiveAfter))
          (negativeAvatar ++ positiveAvatar) := by
  intro negativeClause positiveClause
  exact Or.elim negativeClause
    (fun negativeRegular => Or.elim positiveClause
      (fun positiveRegular => Or.inl
        (Clause.resolveNegatedFirst literal
          negativeBefore negativeAfter positiveBefore positiveAfter
          negativeRegular positiveRegular))
      (fun positiveAvatarProof => Or.inr
        (Clause.appendRight negativeAvatar positiveAvatar positiveAvatarProof)))
    (fun negativeAvatarProof => Or.inr
      (Clause.appendLeft negativeAvatar positiveAvatar negativeAvatarProof))

end AClause

/-- Soundness of equality resolution after unification.

The backend has already applied the mgu of the two disequality sides, so the
selected literal has the form `term ≠ term`.  That literal is false by
reflexivity and can be removed while every other occurrence retains its
original order. -/
theorem equalityResolve {α : Sort _} (term : α) (before after : List Prop) :
    Holds (before ++ (term ≠ term) :: after) → Holds (before ++ after) := by
  intro clause
  have selectedHead : Holds ((term ≠ term) :: (before ++ after)) :=
    perm (moveToHead before after (term ≠ term)) clause
  exact Or.elim selectedHead
    (fun notReflexive => False.elim (notReflexive rfl))
    id

/-- Remove a reflexive disequality selected by Vampire's
`trivial_inequality_removal` simplification.

This has the same logical content as equality resolution, but its separate
name records the rule actually present in the proof certificate. The `before`
and `after` lists keep every surviving literal at its original occurrence and
in its original order. -/
opaque removeTrivialInequality {α : Sort _} (term : α) (before after : List Prop) :
    Holds (before ++ (term ≠ term) :: after) → Holds (before ++ after) := by
  exact equalityResolve term before after

/-- Equality factoring when the removed equality occurs before the retained
equality in the parent clause.

After the mgu, the two positive equalities share `common` as one side. If the
two remaining sides differ, `difference` holds. If they are equal, transitivity
turns the selected equality into a proof of the retained equality. The latter
already occurs among the remaining parent literals. -/
theorem equalityFactorLeft {α : Sort _}
    (common selectedRight retainedRight : α) (difference : Prop)
    (selectedEquation retainedEquation : Prop)
    (before between after : List Prop)
    (selectedToCommon : selectedEquation → common = selectedRight)
    (retainedFromCommon : common = retainedRight → retainedEquation)
    (differenceProof : selectedRight ≠ retainedRight → difference) :
    Holds (before ++ selectedEquation ::
      (between ++ retainedEquation :: after)) →
    Holds (difference ::
      (before ++ (between ++ retainedEquation :: after))) := by
  intro clause
  have selectedHead : Holds (selectedEquation ::
      (before ++ (between ++ retainedEquation :: after))) :=
    perm (moveToHead before (between ++ retainedEquation :: after)
      selectedEquation) clause
  exact Or.elim selectedHead
    (fun selectedProof => by
      by_cases sameRight : selectedRight = retainedRight
      · apply Or.inr
        exact appendRight before _
          (appendRight between _
            (Or.inl (retainedFromCommon ((selectedToCommon selectedProof).trans sameRight))))
      · exact Or.inl (differenceProof sameRight))
    Or.inr

/-- Equality factoring when the removed equality occurs after the retained
equality. This is the positional companion of `equalityFactorLeft`; the result
again starts with the derived disequality and otherwise preserves parent order. -/
theorem equalityFactorRight {α : Sort _}
    (common selectedRight retainedRight : α) (difference : Prop)
    (selectedEquation retainedEquation : Prop)
    (before between after : List Prop)
    (selectedToCommon : selectedEquation → common = selectedRight)
    (retainedFromCommon : common = retainedRight → retainedEquation)
    (differenceProof : selectedRight ≠ retainedRight → difference) :
    Holds (before ++ retainedEquation ::
      (between ++ selectedEquation :: after)) →
    Holds (difference ::
      (before ++ retainedEquation :: (between ++ after))) := by
  intro clause
  have selectedHead : Holds (selectedEquation ::
      (before ++ retainedEquation :: (between ++ after))) :=
    perm (by simpa only [List.append_assoc, List.cons_append] using
      moveToHead (before ++ retainedEquation :: between) after selectedEquation) clause
  exact Or.elim selectedHead
    (fun selectedProof => by
      by_cases sameRight : selectedRight = retainedRight
      · apply Or.inr
        exact appendRight before _
          (Or.inl (retainedFromCommon ((selectedToCommon selectedProof).trans sameRight)))
      · exact Or.inl (differenceProof sameRight))
    Or.inr

/-- Soundness of ground superposition at an arbitrary equality position.

`equation` is a positive equality proposition such as `s = t`. The backend
constructs `rewrite` by replacing every matching ground occurrence in the
rewritten parent clause, using congruence to turn `equation` into an equality
between the complete `source` and `target` clause propositions.

All term unification and occurrence discovery is outside this theorem. By the
time it is applied, Vampire's mgu has already instantiated both parents.
`equalityBefore` and `equalityAfter` expose the position of the equality in
its parent, just as the four tail lists expose the selected positions in
`resolve`. The conclusion keeps the rewritten clause first and appends all
unused equality-parent literals in their original order. -/
theorem superpose (equation : Prop) (source target : List Prop)
    (equalityBefore equalityAfter : List Prop)
    (rewrite : equation → Holds source → Holds target) :
    Holds source → Holds (equalityBefore ++ equation :: equalityAfter) →
      Holds (target ++ (equalityBefore ++ equalityAfter)) := by
  intro sourceClause equationClause
  have equalityHead : Holds (equation :: (equalityBefore ++ equalityAfter)) :=
    perm (moveToHead equalityBefore equalityAfter equation) equationClause
  exact Or.elim equalityHead
    (fun equationProof =>
      appendLeft target (equalityBefore ++ equalityAfter)
        (rewrite equationProof sourceClause))
    (appendRight target (equalityBefore ++ equalityAfter))

namespace AClause

/-- Ground superposition on the regular halves of two A-clauses.

The equality and the rewritten literals live in the regular halves. The
AVATAR halves are propositional context: if either one already holds, it is
embedded unchanged in the result; otherwise `Clause.superpose` performs the
ordinary first-order rewrite and both AVATAR lists are retained in parent
order. This is the A-clause analogue of `Clause.superpose`, kept as a named
opaque bridge so generated replay terms do not expose the case analysis. -/
opaque superpose (equation : Prop) (source target : List Prop)
    (equalityBefore equalityAfter : List Prop)
    (sourceAvatar equalityAvatar : List Prop)
    (rewrite : equation → Clause.Holds source → Clause.Holds target) :
    Holds source sourceAvatar →
      Holds (equalityBefore ++ equation :: equalityAfter) equalityAvatar →
        Holds (target ++ (equalityBefore ++ equalityAfter))
          (sourceAvatar ++ equalityAvatar) := by
  intro sourceClause equalityClause
  exact Or.elim sourceClause
    (fun sourceRegular => Or.elim equalityClause
      (fun equalityRegular => Or.inl
        (Clause.superpose equation source target equalityBefore equalityAfter rewrite
          sourceRegular equalityRegular))
      (fun equalityAvatarProof => Or.inr
        (Clause.appendRight sourceAvatar equalityAvatar equalityAvatarProof)))
    (fun sourceAvatarProof => Or.inr
      (Clause.appendLeft sourceAvatar equalityAvatar sourceAvatarProof))

end AClause

/-- Soundness of forward demodulation by a unit positive equality.

Unlike superposition, demodulation uses its equality parent only as a rewrite
rule and does not append any literals from that parent to the conclusion.  The
backend has already instantiated the rule and constructs `rewrite` by replacing
all matching occurrences in the source clause. -/
theorem demodulate (equation : Prop) (source target : List Prop)
    (rewrite : equation → Holds source → Holds target) :
    Holds source → Holds [equation] → Holds target := by
  intro sourceClause equationClause
  exact Or.elim equationClause
    (fun equationProof => rewrite equationProof sourceClause)
    False.elim

namespace AClause

/-- Forward demodulation on the regular halves of two A-clauses.

The equality parent is unit on its regular side. Its AVATAR literals are still
logical alternatives, so they join the rewritten parent's AVATAR context in
the result. This makes forward demodulation follow the same A-clause contract
as resolution and superposition. -/
opaque demodulate (equation : Prop) (source target : List Prop)
    (sourceAvatar equalityAvatar : List Prop)
    (rewrite : equation → Clause.Holds source → Clause.Holds target) :
    Holds source sourceAvatar → Holds [equation] equalityAvatar →
      Holds target (sourceAvatar ++ equalityAvatar) := by
  intro sourceClause equalityClause
  exact Or.elim sourceClause
    (fun sourceRegular => Or.elim equalityClause
      (fun equalityRegular => Or.inl
        (Clause.demodulate equation source target rewrite sourceRegular equalityRegular))
      (fun equalityAvatarProof => Or.inr
        (Clause.appendRight sourceAvatar equalityAvatar equalityAvatarProof)))
    (fun sourceAvatarProof => Or.inr
      (Clause.appendLeft sourceAvatar equalityAvatar sourceAvatarProof))

end AClause

/-! ## Extensional clause semantics

Resolution needs occurrence-sensitive lists, but the truth of a disjunction is
idempotent: duplicating a literal cannot change whether the clause holds. The
two helpers make that distinction explicit for the extensional theorem below.
-/

/-- A true clause contains a true literal. -/
private theorem existsTrueLiteral : ∀ (literals : List Prop),
    Holds literals → ∃ literal, literal ∈ literals ∧ literal
  | [], proof => False.elim proof
  | literal :: rest, proof =>
    Or.elim proof
      (fun proof => ⟨literal, List.Mem.head _, proof⟩)
      (fun proof => let ⟨found, member, holds⟩ := existsTrueLiteral rest proof
        ⟨found, List.Mem.tail _ member, holds⟩)

/-- A true member makes the whole clause true. -/
private theorem holdsOfTrueLiteral : ∀ (literals : List Prop) (literal : Prop),
    literal ∈ literals → literal → Holds literals
  | [], _, member, _ => False.elim (List.not_mem_nil member)
  | head :: rest, literal, member, proof => by
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl proof
    · exact Or.inr (holdsOfTrueLiteral rest literal member proof)

/-- Evidence that every literal of `source` already occurs in `target`.

This is an explicit, proof-term-friendly form of list containment.  It does
not consume target occurrences: clauses are interpreted as disjunctions, so
two equal occurrences in `source` may both be witnessed by one occurrence in
`target`.  That behavior is exactly what forward subsumption resolution needs. -/
inductive Contained (target : List Prop) : List Prop → Prop where
  /-- The empty clause contributes no literals. -/
  | nil : Contained target []
  /-- Record where the head literal occurs, then certify the remaining tail. -/
  | cons {literal : Prop} {rest : List Prop} :
      literal ∈ target → Contained target rest → Contained target (literal :: rest)

/-- Transport a clause proof to a list containing all of its literals.

Unlike occurrence-sensitive first-order inferences, this theorem has
set-like semantics: several source literals may use one target occurrence.
It is public because AVATAR contexts use the same extensional interpretation.
-/
theorem containedHolds {source target : List Prop}
    (contained : Contained target source) : Holds source → Holds target := by
  induction contained with
  | nil =>
    intro impossible
    exact False.elim impossible
  | @cons literal rest member _ induction =>
    intro proof
    exact Or.elim proof
      (fun literalProof => holdsOfTrueLiteral target literal member literalProof)
      induction

/-- Forward subsumption resolution when the selected main-clause literal is
`literal` and the selected side-clause literal is `¬ literal`.

Ordinary resolution would append `sideBefore ++ sideAfter` to the main
remainder.  The `Contained` certificate says those side literals already
occur in the main remainder, so the smaller main remainder is itself a sound
conclusion.  Both selected positions remain explicit. -/
theorem forwardSubsumptionResolveLiteral (literal : Prop)
    (mainBefore mainAfter sideBefore sideAfter : List Prop)
    (contained : Contained (mainBefore ++ mainAfter) (sideBefore ++ sideAfter)) :
    Holds (mainBefore ++ literal :: mainAfter) →
      Holds (sideBefore ++ (¬ literal) :: sideAfter) →
        Holds (mainBefore ++ mainAfter) := by
  intro mainClause sideClause
  have mainHead : Holds (literal :: (mainBefore ++ mainAfter)) :=
    perm (moveToHead mainBefore mainAfter literal) mainClause
  have sideHead : Holds ((¬ literal) :: (sideBefore ++ sideAfter)) :=
    perm (moveToHead sideBefore sideAfter (¬ literal)) sideClause
  exact Or.elim mainHead
    (fun literalProof => Or.elim sideHead
      (fun notLiteral => False.elim (notLiteral literalProof))
      (containedHolds contained))
    id

/-- Forward subsumption resolution with the opposite polarity: the selected
main occurrence is `¬ literal` and the side occurrence is `literal`. -/
theorem forwardSubsumptionResolveNegatedLiteral (literal : Prop)
    (mainBefore mainAfter sideBefore sideAfter : List Prop)
    (contained : Contained (mainBefore ++ mainAfter) (sideBefore ++ sideAfter)) :
    Holds (mainBefore ++ (¬ literal) :: mainAfter) →
      Holds (sideBefore ++ literal :: sideAfter) →
        Holds (mainBefore ++ mainAfter) := by
  intro mainClause sideClause
  have mainHead : Holds ((¬ literal) :: (mainBefore ++ mainAfter)) :=
    perm (moveToHead mainBefore mainAfter (¬ literal)) mainClause
  have sideHead : Holds (literal :: (sideBefore ++ sideAfter)) :=
    perm (moveToHead sideBefore sideAfter literal) sideClause
  exact Or.elim mainHead
    (fun notLiteral => Or.elim sideHead
      (fun literalProof => False.elim (notLiteral literalProof))
      (containedHolds contained))
    id

namespace AClause

/-- Forward subsumption on the regular halves of two A-clauses when the main
selected literal is positive. The regular side uses the ordinary checked
subsumption theorem; AVATAR evidence from either parent is copied to the
appended AVATAR context. -/
opaque forwardSubsumptionResolveLiteral (literal : Prop)
    (mainBefore mainAfter sideBefore sideAfter : List Prop)
    (mainAvatar sideAvatar : List Prop)
    (contained : Clause.Contained (mainBefore ++ mainAfter) (sideBefore ++ sideAfter)) :
    Holds (mainBefore ++ literal :: mainAfter) mainAvatar →
      Holds (sideBefore ++ (¬ literal) :: sideAfter) sideAvatar →
        Holds (mainBefore ++ mainAfter) (mainAvatar ++ sideAvatar) := by
  intro mainClause sideClause
  exact Or.elim mainClause
    (fun mainRegular => Or.elim sideClause
      (fun sideRegular => Or.inl
        (Clause.forwardSubsumptionResolveLiteral literal mainBefore mainAfter
          sideBefore sideAfter contained mainRegular sideRegular))
      (fun sideAvatarProof => Or.inr
        (Clause.appendRight mainAvatar sideAvatar sideAvatarProof)))
    (fun mainAvatarProof => Or.inr
      (Clause.appendLeft mainAvatar sideAvatar mainAvatarProof))

/-- Polarity-reversed companion of
`AClause.forwardSubsumptionResolveLiteral`. -/
opaque forwardSubsumptionResolveNegatedLiteral (literal : Prop)
    (mainBefore mainAfter sideBefore sideAfter : List Prop)
    (mainAvatar sideAvatar : List Prop)
    (contained : Clause.Contained (mainBefore ++ mainAfter) (sideBefore ++ sideAfter)) :
    Holds (mainBefore ++ (¬ literal) :: mainAfter) mainAvatar →
      Holds (sideBefore ++ literal :: sideAfter) sideAvatar →
        Holds (mainBefore ++ mainAfter) (mainAvatar ++ sideAvatar) := by
  intro mainClause sideClause
  exact Or.elim mainClause
    (fun mainRegular => Or.elim sideClause
      (fun sideRegular => Or.inl
        (Clause.forwardSubsumptionResolveNegatedLiteral literal mainBefore mainAfter
          sideBefore sideAfter contained mainRegular sideRegular))
      (fun sideAvatarProof => Or.inr
        (Clause.appendRight mainAvatar sideAvatar sideAvatarProof)))
    (fun mainAvatarProof => Or.inr
      (Clause.appendLeft mainAvatar sideAvatar mainAvatarProof))

end AClause

namespace AClause

/-- Change only the AVATAR context of an A-clause using set equality.

`sourceInTarget` and `targetInSource` express equality of the two list
memberships. The first implication transports the proof; the reverse one is
kept in the theorem interface so every use records that no AVATAR literal was
silently added or removed. Thus replay can preserve TPTP lists for decoding
while treating AVATAR contexts as sets after they enter the clause layer. -/
opaque transportAvatarSet (regular source target : List Prop) :
    Clause.Contained target source → Clause.Contained source target →
      Holds regular source → Holds regular target := by
  intro sourceInTarget _ clause
  exact Or.elim clause Or.inl
    (fun avatarProof => Or.inr (Clause.containedHolds sourceInTarget avatarProof))

/-- Remove Vampire's displayed `$false` disjunct while remaining in A-clause
form. The decoder represents `$false` by an empty regular list, so this is an
identity on the AVATAR-set boundary. -/
opaque avatarContradictionClause (avatar : List Prop) :
    Holds [] avatar → Holds [] avatar := by
  intro clause
  exact clause

end AClause

/-- Clauses with the same literals have the same disjunctive meaning.

This intentionally compares membership rather than `List.Perm`: the theorem
also covers repeated literals, which have separate Vampire occurrences but the
same propositional meaning. -/
theorem containSameLiteralsAreEqual (left right : List Prop) :
    (∀ x, x ∈ left ↔ x ∈ right) → (Holds left ↔ Holds right) := by
  intro sameLiterals
  constructor
  · intro holds
    let ⟨literal, member, literalHolds⟩ := existsTrueLiteral left holds
    exact holdsOfTrueLiteral right literal ((sameLiterals literal).mp member) literalHolds
  · intro holds
    let ⟨literal, member, literalHolds⟩ := existsTrueLiteral right holds
    exact holdsOfTrueLiteral left literal ((sameLiterals literal).mpr member) literalHolds

/-- Ground factoring removes the right of two equal literal occurrences.

The two occurrences remain separate in Vampire's certificate because they
have different positions. At the propositional clause level they have the
same truth value, so deleting either occurrence preserves `Holds`. The
`before`, `between`, and `after` segments make the removed occurrence's
position explicit. -/
theorem factorRight (literal : Prop) (before between after : List Prop) :
    Holds (before ++ (literal :: (between ++ (literal :: after)))) →
      Holds (before ++ (literal :: (between ++ after))) := by
  apply (containSameLiteralsAreEqual _ _ ?_).mp
  intro proposition
  constructor
  · intro member
    rcases List.mem_append.mp member with beforeMember | member
    · exact List.mem_append.mpr (Or.inl beforeMember)
    rcases List.mem_cons.mp member with literalMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl literalMember)))
    rcases List.mem_append.mp member with betweenMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl betweenMember)))))
    rcases List.mem_cons.mp member with duplicateMember | afterMember
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl duplicateMember)))
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr afterMember)))))
  · intro member
    rcases List.mem_append.mp member with beforeMember | member
    · exact List.mem_append.mpr (Or.inl beforeMember)
    rcases List.mem_cons.mp member with literalMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl literalMember)))
    rcases List.mem_append.mp member with betweenMember | afterMember
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl betweenMember)))))
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr afterMember)))))))

/-- Ground factoring removes the left of two equal literal occurrences.

Together with `factorRight`, this follows the exact occurrence selected by a
Vampire `removed_literal` certificate without hiding a clause permutation in
the factoring proof. -/
theorem factorLeft (literal : Prop) (before between after : List Prop) :
    Holds (before ++ (literal :: (between ++ (literal :: after)))) →
      Holds (before ++ (between ++ (literal :: after))) := by
  apply (containSameLiteralsAreEqual _ _ ?_).mp
  intro proposition
  constructor
  · intro member
    rcases List.mem_append.mp member with beforeMember | member
    · exact List.mem_append.mpr (Or.inl beforeMember)
    rcases List.mem_cons.mp member with literalMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inl literalMember)))))
    rcases List.mem_append.mp member with betweenMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl betweenMember)))
    rcases List.mem_cons.mp member with duplicateMember | afterMember
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inl duplicateMember)))))
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr afterMember)))))
  · intro member
    rcases List.mem_append.mp member with beforeMember | member
    · exact List.mem_append.mpr (Or.inl beforeMember)
    rcases List.mem_append.mp member with betweenMember | member
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl betweenMember)))))
    rcases List.mem_cons.mp member with literalMember | afterMember
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl literalMember)))
    · exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr afterMember)))))))

/-- Remove the later of two identical literal occurrences.

This is the same propositional contraction used by ground factoring, exposed
under the name of Vampire's `duplicate_literal_removal` rule so generated proof
terms describe the certificate that was actually replayed. -/
opaque removeDuplicateRight (literal : Prop) (before between after : List Prop) :
    Holds (before ++ (literal :: (between ++ (literal :: after)))) →
      Holds (before ++ (literal :: (between ++ after))) := by
  exact factorRight literal before between after

/-- Remove the earlier of two identical literal occurrences. -/
opaque removeDuplicateLeft (literal : Prop) (before between after : List Prop) :
    Holds (before ++ (literal :: (between ++ (literal :: after)))) →
      Holds (before ++ (between ++ (literal :: after))) := by
  exact factorLeft literal before between after

/-- Reorder a clause using a permutation witness. This packages the concrete
permutation proof through `containSameLiteralsAreEqual`, so callers use one
named lemma for a semantic clause reordering. -/
theorem reorder {left right : List Prop} (permutation : left.Perm right) :
    Holds left → Holds right :=
  (containSameLiteralsAreEqual left right
    (fun literal : Prop => @List.Perm.mem_iff Prop literal left right permutation)).mp

/-! ## General splitting

Vampire's general splitting moves the literals `M y` that contain one variable
`y` out of a clause `M y ∨ O` and names them: `sP x̄ ↔ ¬ ∀ y, M y`. Replay
binds `sP` to that value, so both resulting clauses are classical consequences.
`component y` is the clause tree of `M y`, keeping Vampire's literal order. -/

/-- The component clause `M y ∨ sP x̄`, where `sP x̄` stands for `¬ ∀ y, M y`. -/
theorem splittingComponent {β : Sort _} (component : β → Tree) (y : β) :
    Holds ((component y).literals ++ [¬ ∀ z, (component z).denote]) := by
  by_cases holds : (component y).denote
  · exact appendLeft _ _ (Tree.toHolds _ holds)
  · exact appendRight _ _ (Or.inl fun all => holds (all y))

/-- The remainder `O ∨ ¬ sP x̄` of a split clause `∀ y, M y ∨ O`, where `O`
does not mention `y`. -/
theorem splittingRemainder {β : Sort _} (component : β → Tree) (rest : List Prop)
    (base : ∀ y, Holds ((component y).literals ++ rest)) :
    Holds (rest ++ [¬ ¬ ∀ z, (component z).denote]) := by
  by_cases all : ∀ z, (component z).denote
  · exact appendRight _ _ (Or.inl fun notAll => notAll all)
  · apply appendLeft
    apply Classical.byContradiction
    intro notRest
    exact all fun z => Or.elim (splitAppend _ _ (base z))
      (Tree.fromHolds _) (fun restProof => absurd restProof notRest)

end VampireHammer.Clause

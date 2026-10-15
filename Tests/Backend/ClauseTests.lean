import VampireHammer.Clause

open VampireHammer.Clause

example (P Q : Prop) (h : P ∨ ¬ Q) :
    SignedLiteral.clause
      [{ atom := P, positive := true }, { atom := Q, positive := false }] = true := by
  apply SignedLiteral.toBoolean
  exact h.elim Or.inl (fun notQ => Or.inr (Or.inl notQ))

example (P Q : Prop) (notP : ¬ P) (notQ : ¬ Q) (h : Holds [P, Q]) : False := by
  exact AllFalse.notHolds (.cons P [Q] notP (.cons Q [] notQ .nil)) h

example (P Q R : Prop) (notP : ¬ P) (notR : ¬ R) (h : Holds [P, Q, R]) : Q := by
  exact unitOfFalse [P] [R] Q (.cons P [] notP .nil) (.cons R [] notR .nil) h

/-! Small kernel checks for the list-clause resolution axiom. The backend test
in `ResolutionExample.lean` exercises the same theorem after parsing a real
Vampire certificate with nonzero literal indices and nontrivial `Or` trees. -/

example (A B C D : Prop) :
    Holds [A, B, C] → Holds [¬ A, D] → Holds [B, C, D] := by
  exact resolve A [] [B, C] [] [D]

example (A B C D : Prop) :
    Holds [B, A, C] → Holds [D, ¬ A] → Holds [B, C, D] := by
  exact resolve A [B] [C] [D] []

example (A B : Prop) :
    Holds [A] → Holds [¬ A, B] → Holds [B] := by
  exact resolve A [] [] [] [B]

example (A : Prop) :
    Holds [A] → Holds [¬ A] → Holds [] := by
  exact resolve A [] [] [] []

/-! Resolution must not swap proof-DAG parents simply because the first
selected literal is negative. `resolveNegatedFirst` preserves the first
parent's tail before the second parent's tail. -/

example (A B C D : Prop) :
    Holds [¬ A, B, C] → Holds [D, A] → Holds [B, C, D] := by
  exact resolveNegatedFirst A [] [B, C] [D] []

/-! An A-clause keeps two clause lists. Resolution indexes only the regular
list and carries the AVATAR list into the result. -/

example (A B C S : Prop) :
    AClause.Holds [A, B] [S] → Holds [¬ A, C] →
      AClause.Holds [B, C] [S] := by
  intro first second
  exact AClause.resolve A [] [B] [] [C] [S] []
    first (AClause.ofFirstOrder [¬ A, C] second)

example (A B C S : Prop) :
    AClause.Holds [¬ A, B] [S] → Holds [C, A] →
      AClause.Holds [B, C] [S] := by
  intro first second
  exact AClause.resolveNegatedFirst A [] [B] [C] [] [S] []
    first (AClause.ofFirstOrder [C, A] second)

/-! The regular A-clause list remains positional, but the AVATAR half is an
extensional set. Reordering it or repeating a split literal is therefore a
named semantic transport rather than an AC reconstruction obligation. -/

example (A S T : Prop) :
    AClause.Holds [A] [S, T] → AClause.Holds [A] [T, S, S] := by
  intro clause
  apply AClause.transportAvatarSet [A] [S, T] [T, S, S]
  · exact .cons (by simp) (.cons (by simp) .nil)
  · exact .cons (by simp) (.cons (by simp) (.cons (by simp) .nil))
  · exact clause

/-! Forward subsumption keeps only the main parent's remainder. The side
clause may have several literals, provided all literals other than the
complementary selection already occur in that main remainder. These examples
also exercise nonzero selected positions and both literal polarities. -/

example (A B C D : Prop) :
    Holds [B, A, C, D] → Holds [C, ¬ A, D] → Holds [B, C, D] := by
  apply forwardSubsumptionResolveLiteral A [B] [C, D] [C] [D]
  exact .cons (by simp) (.cons (by simp) .nil)

example (A B C : Prop) :
    Holds [B, ¬ A, C] → Holds [C, A] → Holds [B, C] := by
  apply forwardSubsumptionResolveNegatedLiteral A [B] [C] [C] []
  exact .cons (by simp) .nil

example (A B C S : Prop) :
    Holds [B, A, C] → AClause.Holds [C, ¬ A] [S] →
      AClause.Holds [B, C] [S] := by
  intro main side
  apply AClause.forwardSubsumptionResolveLiteral A [B] [C] [C] [] [] [S]
  · exact .cons (by simp) .nil
  · exact AClause.ofFirstOrder [B, A, C] main
  · exact side

example (A B : Prop) : Holds [A, A, B] ↔ Holds [A, B] := by
  apply containSameLiteralsAreEqual
  intro literal
  simp

/-! Equality resolution is the unary deletion rule: after unification, its
selected disequality is definitionally `a ≠ a` and hence cannot hold. -/

example {α : Type} (a : α) (P Q : Prop) :
    Holds [P, a ≠ a, Q] → Holds [P, Q] := by
  exact equalityResolve a [P] [Q]

/-! The two equality-factoring lemmas cover both relative positions of the
selected equality.  Their conclusions retain the other equality in place and
put the transitivity side condition at the head of the clause. -/

example {α : Type} (common selectedRight retainedRight : α) (P Q : Prop) :
    Holds [common = selectedRight, P, common = retainedRight, Q] →
      Holds [selectedRight ≠ retainedRight, P, common = retainedRight, Q] := by
  exact equalityFactorLeft common selectedRight retainedRight
    (selectedRight ≠ retainedRight) (common = selectedRight)
    (common = retainedRight) [] [P] [Q] id id id

example {α : Type} (common selectedRight retainedRight : α) (P Q : Prop) :
    Holds [common = retainedRight, P, common = selectedRight, Q] →
      Holds [selectedRight ≠ retainedRight, common = retainedRight, P, Q] := by
  exact equalityFactorRight common selectedRight retainedRight
    (selectedRight ≠ retainedRight) (common = selectedRight)
    (common = retainedRight) [] [P] [Q] id id id

/-! Demodulation consumes a unit equality and rewrites the certificate-selected
literal. Equal terms in other literals remain unchanged. The backend constructs
this `rewrite` argument with congruence after checking every occurrence in that
literal against Vampire's displayed conclusion. -/

example {α : Type} (a b : α) (P Q : α → Prop) :
    Holds [P a, Q a] → Holds [a = b] → Holds [P b, Q a] := by
  apply demodulate (a = b) [P a, Q a] [P b, Q a]
  intro equality source
  exact Eq.mp (congrArg (fun value => Holds [P value, Q a]) equality) source

/-! The remaining first-order calculus rules use the same representation
contract for A-clauses: work on the regular list, then carry AVATAR literals
unchanged. These direct kernel checks cover the named two-parent bridges and
the unary `mapFirstOrder` lift used by factoring and equality resolution. -/

example {α : Type} (a b : α) (P : α → Prop) (S : Prop) :
    AClause.Holds [P a] [S] → Holds [a = b] → AClause.Holds [P b] [S] := by
  intro source equality
  apply AClause.superpose (a = b) [P a] [P b] [] [] [S] []
  · intro equation regular
    exact Eq.mp (congrArg (fun value => Holds [P value]) equation) regular
  · exact source
  · exact AClause.ofFirstOrder [a = b] equality

example {α : Type} (a b : α) (P Q : α → Prop) (S : Prop) :
    AClause.Holds [P a, Q a] [S] → Holds [a = b] → AClause.Holds [P b, Q a] [S] := by
  intro source equality
  apply AClause.demodulate (a = b) [P a, Q a] [P b, Q a] [S] []
  · intro equation regular
    exact Eq.mp (congrArg (fun value => Holds [P value, Q a]) equation) regular
  · exact source
  · exact AClause.ofFirstOrder [a = b] equality

example {α : Type} (a : α) (P S : Prop) :
    AClause.Holds [P, a ≠ a] [S] → AClause.Holds [P] [S] := by
  apply AClause.mapFirstOrder [P, a ≠ a] [P] [S]
  exact equalityResolve a [P] []

example (P S : Prop) : AClause.Holds [P, P] [S] → AClause.Holds [P] [S] := by
  apply AClause.mapFirstOrder [P, P] [P] [S]
  exact factorRight P [] [] []

example {α : Type} (common selectedRight retainedRight : α) (S : Prop) :
    AClause.Holds [common = selectedRight, common = retainedRight] [S] →
      AClause.Holds [selectedRight ≠ retainedRight, common = retainedRight] [S] := by
  apply AClause.mapFirstOrder
  exact equalityFactorLeft common selectedRight retainedRight
    (selectedRight ≠ retainedRight) (common = selectedRight)
    (common = retainedRight) [] [] [] id id id

/-! Vampire may print a rewritten disequality with the equality below `Not`
in the opposite orientation.  This is a pointwise logical equivalence and
does not change the order of clause occurrences. -/

example {α : Type} (a b : α) : Holds [a ≠ b] → Holds [b ≠ a] := by
  exact map (.cons ne_comm .nil)

/-! The replay backend applies the preceding pointwise `Clause.map` bridge
before an inference only when the certificate needs equality symmetry.  These
small checks mirror the three remaining shapes: a factor/duplicate pair and a
forward-subsumption side remainder.  In each case the list order is unchanged;
only the named equality occurrence changes from `b = a` to `a = b`. -/

example {α : Type} (a b : α) (P : Prop) :
    Holds [a = b, b = a, P] → Holds [a = b, P] := by
  intro clause
  have aligned : Holds [a = b, a = b, P] :=
    map (.cons Iff.rfl (.cons eq_comm (.cons Iff.rfl .nil))) clause
  exact factorRight (a = b) [] [] [P] aligned

example {α : Type} (a b : α) (P : Prop) :
    Holds [a ≠ b, b ≠ a, P] → Holds [a ≠ b, P] := by
  intro clause
  have aligned : Holds [a ≠ b, a ≠ b, P] :=
    map (.cons Iff.rfl (.cons ne_comm (.cons Iff.rfl .nil))) clause
  exact removeDuplicateRight (a ≠ b) [] [] [P] aligned

example {α : Type} (a b : α) (A R : Prop) :
    Holds [R, A, b = a] → Holds [¬ A, a = b] → Holds [R, b = a] := by
  intro main side
  have alignedSide : Holds [¬ A, b = a] :=
    map (.cons Iff.rfl (.cons eq_comm .nil)) side
  apply forwardSubsumptionResolveLiteral A [R] [b = a] [] [b = a]
  · exact .cons (by simp) .nil
  · exact main
  · exact alignedSide

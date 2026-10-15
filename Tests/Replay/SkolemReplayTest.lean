import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true
set_option vampire.outputPath "artifacts/skolem-replay-multi.p"
set_option trace.vampire.replay true

/-!
Regression test for proof-local Vampire Skolem symbols.  In contrast to
`SkolemizationExample`, the negated conclusion is deliberately left in place.
Vampire first performs `ennf_transformation` and then introduces several
`sK…` constants in one `skolemize` node.  Replay must reconstruct that derived
parent, introduce nested local lets, and only then decode the Skolemized step.
-/

class TestMagma (α : Type _) where
  op : α → α → α

infix:65 " ⋄ " => TestMagma.op

abbrev Equation650' (G : Type _) [TestMagma G] :=
  ∀ x y z : G, x = x ⋄ (y ⋄ ((z ⋄ x) ⋄ y))

abbrev Equation448' (G : Type _) [TestMagma G] :=
  ∀ x y z : G, x = x ⋄ (y ⋄ (z ⋄ (x ⋄ z)))

theorem multiSkolemReplay (G : Type _) [Nonempty G] [TestMagma G]
    (h : Equation650' G) : Equation448' G := by
  vampire [*]

/-!
Here the two counterexample variables begin in different branches of a
conjunction after ENNF. This exercises occurrence matching across connective
branches rather than the single quantified block in `multiSkolemReplay`. -/
set_option vampire.outputPath "artifacts/skolem-replay-branches.p"

theorem branchedSkolemReplay {α β : Type} [Nonempty α] [Nonempty β] (P : α → Prop) (Q : β → Prop)
    (hP : ∀ x, P x) (hQ : ∀ y, Q y) : (∀ x, P x) ∨ (∀ y, Q y) := by
  vampire [*]

/-!
The negation of this existential-universal conclusion is `∀ x, ∃ y, ¬ R x y`.
Because that form appears only after the goal is negated, it reaches Vampire
unskolemized and asks it to introduce a Skolem *function* of `x`.  This checks
the `Classical.skolem` part of the explicit replay path, not merely constants.
-/
set_option vampire.outputPath "artifacts/skolem-replay-function.p"

theorem functionalSkolemReplay {α β : Type} [Nonempty α] [Nonempty β]
    (R : α → β → Prop) (h : ∃ x, ∀ y, R x y) : ∃ x, ∀ y, R x y := by
  vampire [*]

import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

private opaque classPredicate : Nat → Prop := fun _ => True

class PropositionParent (n : Nat) : Prop where
  law : classPredicate n

class PropositionChild (n : Nat) : Prop extends PropositionParent n

set_option vampire.outputPath "artifacts/proposition-class-law.p" in
theorem proposition_class_law (n : Nat) [PropositionChild n] : classPredicate n := by
  vampire

set_option vampire.outputPath "artifacts/proposition-class-parent.p" in
theorem proposition_class_parent (n : Nat) [PropositionChild n] : PropositionParent n := by
  vampire

-- Nonempty is a class but has no structure metadata. Inspecting its fields
-- must not call the partial getStructureInfo API or lose its witness.
set_option vampire.outputPath "artifacts/proposition-class-nonempty.p" in
theorem proposition_class_nonempty {α : Type} [Nonempty α] (P : α → Prop)
    (positive : ∀ x, P x) (negative : ∀ x, ¬P x) : False := by
  vampire [positive, negative]

#print axioms proposition_class_law
#print axioms proposition_class_parent
#print axioms proposition_class_nonempty

import VampireHammer
import Mathlib.Data.Set.Function
import Mathlib.Algebra.Group.Basic

/-!
Small, live Lean-to-Vampire-to-Lean integration tests using mathlib definitions
and explicitly selected premises. No theorem under test is supplied as a hint,
and every proof ends with `vampire`, without a fallback tactic.

Run sequentially with Tests/scripts/run-mathlib-hammer.py. Each theorem retains its
own TF0 input, TSTP output, stderr, and exit status in artifacts/mathlib-hammer.
The runner caps Vampire memory in both the scheduler and portfolio workers.
-/

set_option vampire.timeLimit 5
set_option vampire.use_portfolio true
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
-- Inhabitation instances are consumed by the exporter, not the final proof.
set_option linter.unusedSectionVars false

namespace MathlibHammerTests

section Sets
variable {α : Type} [Nonempty α]

set_option vampire.outputPath "artifacts/mathlib-hammer/subset_trans.p" in
theorem subset_trans (s t u : Set α) (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/inter_subset.p" in
theorem inter_subset (s t u : Set α) (h : s ⊆ u) : s ∩ t ⊆ u := by
  vampire [h]

set_option vampire.outputPath "artifacts/mathlib-hammer/subset_union.p" in
theorem subset_union (s t u : Set α) (h : s ⊆ t) : s ⊆ t ∪ u := by
  vampire [h]

set_option vampire.outputPath "artifacts/mathlib-hammer/union_subset.p" in
theorem union_subset (s t u : Set α) (hs : s ⊆ u) (ht : t ⊆ u) : s ∪ t ⊆ u := by
  vampire [hs, ht]

set_option vampire.outputPath "artifacts/mathlib-hammer/subset_inter.p" in
theorem subset_inter (s t u : Set α) (ht : s ⊆ t) (hu : s ⊆ u) : s ⊆ t ∩ u := by
  vampire [ht, hu]

set_option vampire.outputPath "artifacts/mathlib-hammer/diff_subset.p" in
theorem diff_subset (s t u : Set α) (h : s ⊆ u) : s \ t ⊆ u := by
  vampire [h]

set_option vampire.outputPath "artifacts/mathlib-hammer/compl_antitone.p" in
theorem compl_antitone (s t : Set α) (h : s ⊆ t) : tᶜ ⊆ sᶜ := by
  vampire [h]

set_option vampire.outputPath "artifacts/mathlib-hammer/disjoint_subset.p" in
theorem disjoint_subset (s t u : Set α) (h : s ⊆ t) (hd : Disjoint t u) :
    Disjoint s u := by
  simp only [Set.disjoint_left] at hd ⊢
  vampire [h, hd]

end Sets

section Functions
variable {α β γ : Type} [Nonempty α] [Nonempty β] [Nonempty γ]

set_option vampire.outputPath "artifacts/mathlib-hammer/injective_comp.p" in
theorem injective_comp (f : α → β) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  vampire [*]

set_option vampire.outputPath "artifacts/mathlib-hammer/surjective_comp.p" in
theorem surjective_comp (f : α → β) (g : β → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  vampire [*]

set_option vampire.outputPath "artifacts/mathlib-hammer/injective_of_left_inverse.p" in
theorem injective_of_left_inverse (f : α → β) (g : β → α)
    (h : Function.LeftInverse g f) : Function.Injective f := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/surjective_of_right_inverse.p" in
theorem surjective_of_right_inverse (f : α → β) (g : β → α)
    (h : Function.RightInverse g f) : Function.Surjective f := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/injective_comp_cancel.p" in
theorem injective_comp_cancel (f : α → β) (g : β → γ)
    (h : Function.Injective (g ∘ f)) : Function.Injective f := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/preimage_mono.p" in
theorem preimage_mono (f : α → β) (s t : Set β) (h : s ⊆ t) :
    f ⁻¹' s ⊆ f ⁻¹' t := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/image_mono.p" in
theorem image_mono (f : α → β) (s t : Set α) (h : s ⊆ t) :
    f '' s ⊆ f '' t := by
  vampire [h]

set_option vampire.outputPath "artifacts/mathlib-hammer/image_preimage_subset.p" in
theorem image_preimage_subset (f : α → β) (s : Set β) : f '' (f ⁻¹' s) ⊆ s := by
  vampire []

end Functions

section Orders
variable {α : Type} [PartialOrder α] [Nonempty α]

set_option vampire.outputPath "artifacts/mathlib-hammer/le_of_le_of_eq.p" in
theorem le_of_le_of_eq (a b c : α) (hab : a ≤ b) (hbc : b = c) : a ≤ c := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/le_chain.p" in
theorem le_chain (a b c d : α) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/eq_of_le_chain.p" in
theorem eq_of_le_chain (a b c : α) (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = c := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/monotone_chain.p" in
theorem monotone_chain (f : α → α) (hf : Monotone f) (a b c : α)
    (hab : a ≤ b) (hbc : b ≤ c) : f a ≤ f c := by
  vampire

end Orders

section Algebra
variable {G : Type} [Group G]

set_option vampire.outputPath "artifacts/mathlib-hammer/inverse_cancel.p" in
theorem inverse_cancel (a b : G) : a⁻¹ * (a * b) = b := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/mul_left_cancel.p" in
theorem mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/mul_right_cancel.p" in
theorem mul_right_cancel (a b c : G) (h : b * a = c * a) : b = c := by
  vampire

set_option vampire.outputPath "artifacts/mathlib-hammer/solve_mul_eq.p" in
theorem solve_mul_eq (a b c : G) (h : a * b = c) : b = a⁻¹ * c := by
  vampire

end Algebra

-- Audit representatives of universal, existential, ordered, and algebraic proofs.
#print axioms subset_trans
#print axioms surjective_comp
#print axioms eq_of_le_chain
#print axioms mul_left_cancel

end MathlibHammerTests

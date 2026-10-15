import VampireHammer
import Mathlib.Data.Finset.SymmDiff

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- Domain rules are caller-supplied hints, not part of the tactic. The element
-- type can be empty: membership binders supply actual elements.
set_option vampire.outputPath "artifacts/finset-sdiff-symmDiff.p" in
theorem finset_sdiff_symmDiff {α : Type} [DecidableEq α] (s t : Finset α) :
    t \ s ⊆ symmDiff s t := by
  vampire [Finset.mem_sdiff, Finset.mem_symmDiff]

set_option vampire.outputPath "artifacts/finset-inter-diff.p" in
theorem finset_inter_diff {α : Type} [DecidableEq α] (a b c : Finset α) :
    (a ∩ b) \ c = a ∩ (b \ c) := by
  apply Finset.ext
  intro x
  vampire [Finset.mem_sdiff, Finset.mem_inter]

-- Explicit subset and membership facts must also work with local hypotheses.
set_option vampire.outputPath "artifacts/finset-subset-hypothesis.p" in
theorem finset_subset_hypothesis {α : Type} [DecidableEq α]
    (a b c : Finset α) (subset : a ⊆ b) : a \ c ⊆ b := by
  vampire [subset, Finset.mem_sdiff, Finset.subset_iff]

section RegisteredFacts

-- This theorem has no simp/grind attribute in mathlib. Registering it locally
-- makes it available through the ordinary index, without changing the hammer.
attribute [local simp] Finset.mem_symmDiff

set_option vampire.outputPath "artifacts/finset-registered-facts.p" in
theorem finset_registered_facts {α : Type} [DecidableEq α] (s t : Finset α) :
    t \ s ⊆ symmDiff s t := by
  vampire []

end RegisteredFacts

set_option vampire.outputPath "artifacts/finset-export.p" in
example {α : Type} [DecidableEq α] (s t : Finset α) (subset : s ⊆ t) : s ⊆ t := by
  vampire_export [subset]
  exact subset

#print axioms finset_sdiff_symmDiff
#print axioms finset_inter_diff
#print axioms finset_subset_hypothesis
#print axioms finset_registered_facts

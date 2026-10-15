import VampireHammer

set_option vampire.attributeLemmas false

universe u

set_option vampire.outputPath "artifacts/sort-replay/general.p" in
theorem sort_resolution {α : Sort u} (R : α → α → Prop) (a b c : α)
    (trans : ∀ x y z, R x y → R y z → R x z)
    (ab : R a b) (bc : R b c) : R a c := by
  vampire [trans, ab, bc]

-- Concrete Prop-valued domains must also keep their original universe.
set_option vampire.outputPath "artifacts/sort-replay/prop.p" in
theorem prop_resolution (R : True → True → Prop) (a b c : True)
    (trans : ∀ x y z, R x y → R y z → R x z)
    (ab : R a b) (bc : R b c) : R a c := by
  vampire [trans, ab, bc]

#print axioms sort_resolution
#print axioms prop_resolution

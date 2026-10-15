import VampireHammer

/-!
End-to-end test for the resolution variants with substitution certificates:
unit-resulting, extensionality, constrained and backward subsumption
resolution, forward literal rewriting, subsumption equality resolution, and
condensation. The mock proof derives one clause with each rule; the trace
shows whether each was reconstructed directly.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-resolution-variants.sh"
set_option vampire.outputPath "artifacts/resolution-variants.p"
set_option trace.vampire.replay true

theorem resolutionVariants {α : Type} (a b : α) (f : α → α)
    (P Q S T U V Y Z : α → Prop) (W : α → α → Prop) (R : Prop)
    (hNucleus : ∀ x, ¬P x ∨ ¬Q x ∨ S x) (hP : P a) (hQ : Q a) (hS : ¬S a)
    (hCondense : ∀ x, T x ∨ T a) (hT : ¬T a)
    (hRewritten : U a ∨ R) (hRule : ∀ x, ¬U x ∨ V x) (hV : ¬V a) (hR : ¬R)
    (hExtensional : ∀ x y, x = y ∨ ¬W x y) (hDistinct : a ≠ b) (hW : W a b)
    (hBackward : ∀ x, ¬U x)
    (hReflexive : ∀ x, x ≠ a ∨ Z x) (hZ : ¬Z a)
    (hConstrained : Y (f a)) (hNotConstrained : ¬Y b) (hEquation : R → f a = b)
    (hDeep : ¬Y (f (f a))) :
    False := by
  vampire [hNucleus, hP, hQ, hS, hCondense, hT, hRewritten, hRule, hV, hR,
    hExtensional, hDistinct, hW, hBackward, hReflexive, hZ, hConstrained,
    hNotConstrained, hEquation, hDeep]

#print axioms resolutionVariants

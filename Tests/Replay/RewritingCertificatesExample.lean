import VampireHammer

/-!
Synthetic end-to-end test for backward demodulation, subsumption demodulation,
inner rewriting, and constrained superposition with the new Vampire replay
annotation shapes. The fixture retains the naming regressions and uses
explicit weakening scaffolds to isolate the four rewrite rules. Replay traces
distinguish their dedicated handlers from those scaffolds.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-fixture.sh"
set_option vampire.strategy "rewriting-certificates"
set_option vampire.outputPath "artifacts/rewriting-certificates.p"
set_option trace.vampire.replay true

theorem rewritingCertificates {α : Type} (a : α) (f g : α → α)
    (P Q : α → α → Prop) (U V W D E F R : α → Prop)
    (hSplit : ∀ x y z, P x y ∨ Q y z)
    (hIneq : ∀ x, f x ≠ a ∨ U x) (hIneqFlipped : ∀ x, a ≠ f x ∨ V x)
    (hProxy : ∀ x, f x = a ∨ W x)
    (hDefinition : (∀ x, g x = f (f x)) ∧ W a) (hUse : ∀ x, R (g x)) (hNotR : ¬R (f (f a)))
    (hPredicate : (∀ x, D x ↔ E x ∨ F x) ∧ W a) (hD : D a) : False := by
  vampire [hSplit, hIneq, hIneqFlipped, hProxy, hDefinition, hUse, hNotR, hPredicate, hD]

#print axioms rewritingCertificates

-- Until Vampire emits the backward certificate, test the proposed annotation
-- through the full parser/replay pipeline with a synthetic backward-labelled node.
set_option vampire.executable "Tests/testdata/scripts/mock-backward-sd.sh" in
set_option vampire.outputPath "artifacts/backward-sd-certificates.p" in
theorem backwardSubsumptionCertificates {α : Type} (a : α) (f g : α → α)
    (P Q : α → α → Prop) (U V W D E F R : α → Prop)
    (hSplit : ∀ x y z, P x y ∨ Q y z)
    (hIneq : ∀ x, f x ≠ a ∨ U x) (hIneqFlipped : ∀ x, a ≠ f x ∨ V x)
    (hProxy : ∀ x, f x = a ∨ W x)
    (hDefinition : (∀ x, g x = f (f x)) ∧ W a) (hUse : ∀ x, R (g x)) (hNotR : ¬R (f (f a)))
    (hPredicate : (∀ x, D x ↔ E x ∨ F x) ∧ W a) (hD : D a) : False := by
  vampire [hSplit, hIneq, hIneqFlipped, hProxy, hDefinition, hUse, hNotR, hPredicate, hD]


#print axioms backwardSubsumptionCertificates

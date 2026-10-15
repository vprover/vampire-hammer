import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-fixture.sh"
set_option trace.vampire.replay true

set_option vampire.outputPath "artifacts/closure-global.p" in
set_option vampire.strategy "real-global-subsumption" in
theorem closure_global (P Q : Prop)
    (h1 : P ∨ Q) (h2 : P ∨ ¬Q) (h3 : ¬P ∨ Q) (h4 : ¬P ∨ ¬Q) : False := by
  vampire [h1, h2, h3, h4]

set_option vampire.outputPath "artifacts/closure-predicate.p" in
set_option vampire.strategy "real-predicate-elimination" in
theorem closure_predicate {α : Type} (a b : α) (f : α → α) (P W : α → Prop)
    (h1 : ∀ x, f x = a ∨ W x) (h2 : ∀ x, ¬W x) (h3 : ¬P (f b)) (h4 : P a) : False := by
  vampire [h1, h2, h3, h4]

set_option vampire.outputPath "artifacts/closure-euf.p" in
set_option vampire.strategy "euf-conflict" in
theorem closure_euf {α : Type} (a b : α) (f : α → α) (R : Prop)
    (h1 : a = b ∨ R) (h2 : f a ≠ f b) (h3 : ¬R) : False := by
  vampire [h1, h2, h3]

#print axioms closure_global
#print axioms closure_predicate
#print axioms closure_euf

-- A tiny live-recorded AVATAR proof with congruence closure enabled.
set_option vampire.outputPath "artifacts/closure-real-euf.p" in
set_option vampire.strategy "real-euf-conflict" in
theorem closure_real_euf {α : Type} (a b : α) (f : α → α) (R : Prop)
    (h1 : a = b ∨ R) (h2 : f a ≠ f b) (h3 : ¬R) : False := by
  vampire [h1, h2, h3]

#print axioms closure_real_euf

-- The same live proof with explicit FO occurrence/definition mapping.
set_option vampire.outputPath "artifacts/closure-annotated-euf.p" in
set_option vampire.strategy "annotated-euf-conflict" in
theorem closure_annotated_euf {α : Type} (a b : α) (f : α → α) (R : Prop)
    (h1 : a = b ∨ R) (h2 : f a ≠ f b) (h3 : ¬R) : False := by
  vampire [h1, h2, h3]

#print axioms closure_annotated_euf

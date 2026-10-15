import VampireHammer

/-!
Replay of recorded Vampire proofs that use the preprocessing and calculus
rules added for naming, splitting, the equality proxy, and the resolution
variants. Each fixture is the unmodified output of a certificate-emitting Vampire build
for the theorem below, with the strategy in its doc comment, except
where a fixture's header says an `associativity_commutativity` node was added
by hand: Vampire does not yet bridge literal reordering for those rules.
`Tests/testdata/scripts/mock-fixture.sh` prints the fixture named by `vampire.strategy`.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-fixture.sh"
set_option trace.vampire.replay true

-- General splitting (component clause and remainder); recorded with strategy `dis+1_1:1_gsp=on_10`.
set_option vampire.outputPath "artifacts/real-gsp.p" in
set_option vampire.strategy "real-gsp" in
theorem real_gsp {α : Type} (a : α) (P Q : α → α → Prop)
    (h1 : ∀ x y z, P x y ∨ Q y z) (h2 : ∀ x, ¬P x a) (h3 : ∀ z, ¬Q a z) : False := by
  vampire [h1, h2, h3]

-- Inequality splitting; recorded with strategy `dis+1_1:1_ins=1_10`.
set_option vampire.outputPath "artifacts/real-ins.p" in
set_option vampire.strategy "real-ins" in
theorem real_ins {α : Type} (a b : α) (f : α → α) (U V : α → Prop) (W : Prop)
    (h1 : ∀ x, a ≠ f x ∨ U x) (h2 : ∀ x, f x ≠ b ∨ V x) (h3 : ∀ x, ¬U x) (h4 : ∀ x, ¬V x)
    (h5 : W → f a = a) (h6 : W) : False := by
  vampire [h1, h2, h3, h4, h5, h6]

-- The equality proxy; recorded with strategy `dis+1_1:1_ep=RSTC_10`.
set_option vampire.outputPath "artifacts/real-ep.p" in
set_option vampire.strategy "real-ep" in
theorem real_ep {α : Type} (a b : α) (f : α → α) (P W : α → Prop)
    (h1 : ∀ x, f x = a ∨ W x) (h2 : ∀ x, ¬W x) (h3 : ¬P (f b)) (h4 : P a) : False := by
  vampire [h1, h2, h3, h4]

-- Definition unfolding; recorded with strategy `dis+1_1:1_fde=all_10`.
set_option vampire.outputPath "artifacts/real-fde.p" in
set_option vampire.strategy "real-fde" in
theorem real_fde {α : Type} (a : α) (f g : α → α) (R : α → Prop) (W : α → Prop)
    (h1 : (∀ x, g x = f (f x)) ∧ W a) (h2 : ∀ x, R (g x) ∨ R (g (g x))) (h3 : ∀ x, ¬R (f (f x))) :
    False := by
  vampire [h1, h2, h3]

-- Consistent polarity flipping; recorded with strategy `dis+1_1:1_rp=on_10`.
set_option vampire.outputPath "artifacts/real-rp.p" in
set_option vampire.strategy "real-rp" in
theorem real_rp {α : Type} (a : α) (P Q R : α → Prop) (h1 : ∀ x, P x ∨ Q x) (h2 : ∀ x, ¬P x ∨ R x) (h3 : ¬ Q a) (h4 : ¬ R a) : False := by
  vampire [h1, h2, h3, h4]

-- Condensation; recorded with strategy `dis+1_1:1_cond=on_10`.
set_option vampire.outputPath "artifacts/real-cond.p" in
set_option vampire.strategy "real-cond" in
theorem real_cond {α : Type} (a : α) (P : α → α → Prop) (Q : α → Prop) (h1 : ∀ x y, P x a ∨ P y a ∨ Q y) (h2 : ∀ x, ¬ P x a) (h3 : ∀ x, ¬ Q x) : False := by
  vampire [h1, h2, h3]

-- Unit-resulting resolution; recorded with strategy `dis+1_1:1_urr=on:br=off_10`.
set_option vampire.outputPath "artifacts/real-urr.p" in
set_option vampire.strategy "real-urr" in
theorem real_urr {α : Type} (a : α) (P Q S : α → Prop) (h1 : ∀ x, ¬P x ∨ ¬Q x ∨ S x) (h2 : P a) (h3 : Q a) (h4 : ¬ S a) : False := by
  vampire [h1, h2, h3, h4]

-- Constrained resolution; recorded with strategy `dis+1_1:1_uwa=all_10`.
set_option vampire.outputPath "artifacts/real-uwa.p" in
set_option vampire.strategy "real-uwa" in
theorem real_uwa {α : Type} (a b : α) (f : α → α) (Y : α → Prop) (R : Prop) (h1 : Y (f a)) (h2 : ¬ Y b) (h3 : R → f a = b) (h4 : R) : False := by
  vampire [h1, h2, h3, h4]

-- True/false elimination; recorded with strategy `dis+1_1:1_newcnf=off_10`.
set_option vampire.outputPath "artifacts/real-tf.p" in
set_option vampire.strategy "real-tf" in
theorem real_tf {α : Type} (a : α) (P : α → Prop) (A : Prop) (h1 : (A ∧ True) ∨ False) (h2 : A → P a) (h3 : ¬ P a) : False := by
  vampire [h1, h2, h3]

-- Backward subsumption resolution; recorded with strategy `dis+1_1:1_bsr=on:fsr=off:sa=otter_10`.
set_option vampire.outputPath "artifacts/real-bsr.p" in
set_option vampire.strategy "real-bsr" in
theorem real_bsr {α : Type} (a b : α) (P Q : α → Prop) (R : Prop) (h1 : ∀ x, ¬ P x) (h2 : P a ∨ R ∨ Q b) (h3 : ¬ R) (h4 : ¬ Q b) : False := by
  vampire [h1, h2, h3, h4]

-- Forward literal rewriting; recorded with strategy `dis+1_1:1_flr=on:av=off_10`.
set_option vampire.outputPath "artifacts/real-flr.p" in
set_option vampire.strategy "real-flr" in
theorem real_flr {α : Type} (a : α) (P Q : α → Prop) (R S : Prop) (h1 : ∀ x, ¬ P x ∨ Q x) (h2 : ∀ x, ¬ Q x ∨ P x) (h3 : Q a ∨ R ∨ S) (h4 : ¬ P a) (h5 : ¬ R) (h6 : ¬ S) : False := by
  vampire [h1, h2, h3, h4, h5, h6]

-- Extensionality resolution; recorded with strategy `dis+1_1:1_er=filter:br=off_10`.
set_option vampire.outputPath "artifacts/real-er.p" in
set_option vampire.strategy "real-er" in
theorem real_er {α : Type} (a b : α) (W : α → α → Prop) (h1 : ∀ x y, x = y ∨ ¬ W x y) (h2 : a ≠ b) (h3 : W a b) : False := by
  vampire [h1, h2, h3]

-- Subsumption equality resolution; recorded with strategy `dis+1_1:1_ser=on:erd=off_10`.
set_option vampire.outputPath "artifacts/real-ser.p" in
set_option vampire.strategy "real-ser" in
theorem real_ser {α : Type} (a : α) (Z : α → Prop) (Y : Prop) (h1 : ∀ x y, x ≠ a ∨ Z y ∨ Y) (h2 : ∀ y, ¬ Z y) (h3 : ¬ Y) : False := by
  vampire [h1, h2, h3]
#print axioms real_gsp
#print axioms real_ins
#print axioms real_ep
#print axioms real_fde
#print axioms real_rp
#print axioms real_cond
#print axioms real_urr
#print axioms real_uwa
#print axioms real_tf
#print axioms real_bsr
#print axioms real_flr
#print axioms real_er
#print axioms real_ser

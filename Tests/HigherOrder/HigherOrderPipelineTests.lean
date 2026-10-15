import VampireHammer

/-! Complete `vampire` replay of real higher-order proofs printed by the
certificate-emitting Vampire build (see
docs/VAMPIRE_HO_CERTIFICATES.md). Each fixture is that build's unmodified output
for the goal below, run with the rule options noted; `Tests/testdata/scripts/mock-fixture.sh`
replays it, so the exported problem must stay identical. -/

set_option vampire.higherOrder true
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/mock-fixture.sh"

-- `-hud 0`: imitation, projection, and equality resolution leaving residual
-- unification constraints.
set_option vampire.strategy "higher-order/pipeline/imitate0" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-imitate0.p" in
theorem pipeline_imitation (i : Type) (a : i) (f : i → i) : ∃ F : i → i, F a = f (f a) := by
  vampire []

-- Default higher-order unification: unnormalized imitation bindings.
set_option vampire.strategy "higher-order/pipeline/imitate1" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-imitate1.p" in
theorem pipeline_unification (i : Type) (a : i) (f : i → i) : ∃ F : i → i, F a = f (f a) := by
  vampire []

-- `-hud 0`: projection after a negative universal witness.
set_option vampire.strategy "higher-order/pipeline/project0" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-project0.p" in
theorem pipeline_projection (i : Type) (a : i) (f : i → i) (h : ∀ x, f x = x) :
    ∃ F : i → i, ∀ y, F y = f y := by
  vampire [h]

set_option vampire.strategy "higher-order/pipeline/project" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-project.p" in
theorem pipeline_function_witness (i : Type) (a : i) (f : i → i) (h : ∀ x, f x = x) :
    ∃ F : i → i, ∀ y, F y = f y := by
  vampire [h]

-- Primitive instantiation, constrained superposition with a function
-- constraint keeping the rewritten literal in place, and equality factoring
-- with a residual unification constraint.
set_option vampire.strategy "higher-order/pipeline/prim2" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-prim2.p" in
theorem pipeline_primitive_instantiation (i : Type) (a : i) (q : i → Prop) :
    ∃ P : i → Prop, ∀ x, P x ↔ ¬q x := by
  vampire []

-- `--cnf_on_the_fly lazy_simp`: FOOL distinctness axiom.
set_option vampire.strategy "higher-order/pipeline/prim3" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-prim3.p" in
theorem pipeline_fool_distinctness : ∃ P : Prop → Prop, P True ∧ ¬P False := by
  vampire []

-- `-cha on`: negative-universal witness, constraints and flex-flex closure.
set_option vampire.strategy "higher-order/pipeline/choice3" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-choice3.p" in
theorem pipeline_choice_like (i : Type) (a : i) (p : i → Prop) :
    ∃ F : (i → Prop) → i, ∀ x, p x → p (F p) := by
  vampire []

-- `-c on --cnf_on_the_fly lazy_simp`: FOOL exhaustiveness axiom.
set_option vampire.strategy "higher-order/pipeline/cases" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-cases.p" in
theorem pipeline_fool_exhaustiveness (p : Prop → Prop) (q : Prop) (ht : p True) (hf : p False) :
    p q := by
  vampire [ht, hf]

-- `-cs on --cnf_on_the_fly lazy_simp`.
set_option vampire.strategy "higher-order/pipeline/casesimp" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-casesimp.p" in
theorem pipeline_cases_simplifying (p : Prop → Prop) (q : Prop) (ht : p True) (hf : p False) :
    p q := by
  vampire [ht, hf]

-- `-chr on`: the input choice definition is deleted without being linked.
set_option vampire.strategy "higher-order/pipeline/chr" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-chr.p" in
theorem pipeline_choice_reasoning (i : Type) (a : i) (p : i → Prop) (eps : (i → Prop) → i)
    (hdef : ∀ (P : i → Prop) x, P x → P (eps P)) (pa : p a) : p (eps p) := by
  vampire [hdef, pa]

-- `-fe axiom`.
set_option vampire.strategy "higher-order/pipeline/funcext2" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-funcext2.p" in
theorem pipeline_function_congruence (i : Type) (a : i) (f g : i → i) (p : (i → i) → Prop)
    (h : ∀ x, f x = g x) (pf : p f) : p g := by
  vampire [h, pf]

-- `--cnf_on_the_fly lazy_simp`.
set_option vampire.strategy "higher-order/pipeline/quant" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-quant.p" in
theorem pipeline_quantifier_witness (i : Type) (a : i) (p : i → Prop) (q : Prop)
    (h1 : (∃ x, p x) ∨ q) (h2 : ¬q) (h3 : ∀ x, ¬p x) : False := by
  vampire [h1, h2, h3]

set_option vampire.strategy "higher-order/pipeline/leibniz" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-leibniz.p" in
theorem pipeline_leibniz (i : Type) (a b : i) (h : ∀ P : i → Prop, P b → P a) : a = b := by
  vampire [h]

set_option vampire.strategy "higher-order/pipeline/flexflex" in
set_option vampire.outputPath "artifacts/higher-order-pipeline-flexflex.p" in
theorem pipeline_flex_flex (i : Type) (a b : i) (h : ∀ F G : i → i, F a ≠ G b) : False := by
  vampire [h]

#print axioms pipeline_imitation
#print axioms pipeline_unification
#print axioms pipeline_projection
#print axioms pipeline_function_witness
#print axioms pipeline_primitive_instantiation
#print axioms pipeline_fool_distinctness
#print axioms pipeline_choice_like
#print axioms pipeline_fool_exhaustiveness
#print axioms pipeline_cases_simplifying
#print axioms pipeline_choice_reasoning
#print axioms pipeline_function_congruence
#print axioms pipeline_quantifier_witness
#print axioms pipeline_leibniz
#print axioms pipeline_flex_flex

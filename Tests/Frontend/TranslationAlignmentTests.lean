import Mathlib
import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.outputPath "artifacts/translation-alignment.p"
set_option vampire.timeLimit 10
set_option vampire.suggestedLemmas 0
set_option vampire.siblingLemmas false
set_option Elab.async false

-- Library theorems whose exported problems were satisfiable although the
-- original proof uses only the listed premises. Each is restated, so the
-- original theorem is not available as a fact.

-- The argument of a coercion `⇑f x` with `β := fun _ => H` is a term of the
-- problem, not part of an opaque constant (lean-auto `ConstInst.ofExpr?`).
example : type_of% @AddConstMapClass.map_const := by
  intros; vampire [*, AddConstMapClass.map_add_const, zero_add]

-- Definitions are unfolded by one plan for the whole problem
-- (`UnfoldingPlan`): `IsLeftRegular` occurs only in the premise.
example : type_of% @mul_left_cancel := by
  intros; vampire [*, IsLeftCancelMul.mul_left_cancel]
-- `≤` of `SimpleGraph` is written inline in its instance; `deleteEdges`
-- occurs only in the goal.
example : type_of% @SimpleGraph.deleteEdges_mono := by
  intros; vampire [*, sdiff_le_sdiff_right]
example : type_of% @IsSquare.mul_self := by intros; vampire [*]
example : type_of% @Even.add_self := by intros; vampire [*]
-- The premise concludes the folded `IsSheaf`, whose body is not translatable.
example : type_of% @CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize := by
  intros; vampire [*, CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf]

-- Definitional inverses and projections of one-field structures.
example : type_of% @Quiver.Hom.unmop_inj := by intros; vampire [*]
example : type_of% @CategoryTheory.Iso.self_symm_conj := by
  intros; vampire [*, CategoryTheory.Iso.symm_self_conj]

-- Data arguments of premises come from non-proposition hints and local data
-- (`DataWitnesses`).
example : type_of% @ULift.instIsEmpty := by intros; vampire [*, Equiv.isEmpty, Equiv.ulift]
example : type_of% @CategoryTheory.Limits.FormalCoproduct.instFaithfulIncl := by
  intros; vampire [*, CategoryTheory.Functor.FullyFaithful.faithful,
    CategoryTheory.Limits.FormalCoproduct.fullyFaithfulIncl]
example : type_of% @CategoryTheory.Functor.IsRepresentable.mk' := by
  intros; vampire [*, CategoryTheory.Functor.RepresentableBy.isRepresentable,
    CategoryTheory.Functor.representableByEquiv]
example : type_of% @Pi.multiset_prod_apply := by
  intros; vampire [*, MonoidHom.map_multiset_prod, Pi.evalMonoidHom]

-- `Set.image` and `Set.range` are unfolded in every fact alike; the range
-- quantifies over `↥s`, relativized to `∃ a, a ∈ s ∧ …` (`SubtypeRelativization`).
example : type_of% @Set.image_eq_range := by intros; vampire [*, Set.ext]
-- `{1}` at `Set` is planned through the goal's `Singleton.singleton`.
example : type_of% @Set.range_one := by intros; vampire [*, Set.range_const]
-- `0 : ℕ` occurs only in a premise; unfolding it would only rename the numeral.
example : type_of% @Nat.dvd_sub_self_right := by
  intros
  vampire [*, LT.lt.not_ge, Nat.dvd_refl, Nat.dvd_sub_iff_left, Nat.dvd_zero._simp_1,
    Nat.sub_eq_zero_of_le, le_of_lt, le_or_gt]

import Mathlib
import VampireHammer.Benchmark.Mathlib

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.outputPath "artifacts/mathlib-failure-regressions.p"
set_option Elab.async false

-- These original statements failed in the frozen 5,000-lemma corpus. Each
-- attempt must be checked by the kernel without directly or transitively
-- using its original theorem. Failed benchmark commands alone do not make
-- Lean exit with an error, so explicitly validate every recorded result.
#eval IO.FS.writeFile "artifacts/mathlib-failure-regressions.jsonl" ""

hammer_mathlib_try "ZeroHom.neg_apply" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "AddMonoid.End.ofNat_apply" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "CategoryTheory.ShortComplex.FunctorEquivalence.functor_map_app" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "SimplexCategory.revCompRevIso_hom_app" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Function.Periodic.sub_eq'" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "ULift.up_nnratCast" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "CategoryTheory.Triangulated.TStructure.triangleω₁δ_obj_obj₃" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "floorDiv_one" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Set.inter_diff_assoc" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Set.inclusion_le_inclusion" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "SetLike.coe_injective" recording "artifacts/mathlib-failure-regressions.jsonl"
-- DeltaGenerated is now an abbreviation; retain constructor size-of coverage
-- with a category that still has its own structure constructor.
hammer_mathlib_try "Sequential.mk.sizeOf_spec" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Subalgebra.mem_toSubsemiring" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "RingPreordering.mem_mk'" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Set.star_centralizer" recording "artifacts/mathlib-failure-regressions.jsonl"

hammer_mathlib_try "neg_add_lt_iff_lt_add" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "CFC.log.congr_simp" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "csInf_upperBounds_eq_csSup" recording "artifacts/mathlib-failure-regressions.jsonl"

-- Source structure metadata supplies checked projections and extensionality,
-- including proof fields whose types depend on preceding data fields.
-- FourierModule's constructor no longer exists in mathlib 4.34.1.
hammer_mathlib_try "Sequential.mk.injEq" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "OrderRingIso.mk.injEq" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "SSet.Truncated.Edge.CompStruct.mk.injEq" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Flag.mem_rangeFin" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "Nat.cast_eq_one" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "MonoidWithZeroHom.one_apply_eq_zero_iff" recording "artifacts/mathlib-failure-regressions.jsonl"

-- Primitive projection normalization must retain the structure's exact
-- instance parameters, including dependent quotient and subtype fields.
hammer_mathlib_try "Finsupp.Icc_eq" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "PiTensorProduct.liftAlgHom_apply" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "CategoryTheory.ULift.downFunctor_obj" recording "artifacts/mathlib-failure-regressions.jsonl"
hammer_mathlib_try "groupCohomology.isoCocycles₂_hom_comp_i_apply" recording "artifacts/mathlib-failure-regressions.jsonl"

-- Membership expansion must preserve this earlier reflexive success.
hammer_mathlib_try "UnitsInt.univ" recording "artifacts/mathlib-failure-regressions.jsonl"

#eval do
  let lines ← IO.FS.readFile "artifacts/mathlib-failure-regressions.jsonl"
  let mut count := 0
  for line in lines.splitOn "\n" do
    if line.isEmpty then continue
    let json ← IO.ofExcept (Lean.Json.parse line)
    let event ← IO.ofExcept (json.getObjValAs? String "event")
    unless event == "finished" do continue
    count := count + 1
    let name ← IO.ofExcept (json.getObjValAs? String "name")
    let status ← IO.ofExcept (json.getObjValAs? String "status")
    unless status == "proved" do
      throw <| IO.userError s!"{name} failed its independent proof audit: {json.compress}"
    unless ← IO.ofExcept (json.getObjValAs? Bool "kernel_checked") do
      throw <| IO.userError s!"{name} was not kernel checked"
  unless count == 29 do throw <| IO.userError s!"expected twenty-nine results, got {count}"

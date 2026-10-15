import VampireHammer
import VampireHammer.Export.StructureProjections

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.attributeLemmas false

-- Equality of function-valued fields must follow from the source constructor
-- equality, without Nonempty assumptions on either function domain or range.
set_option vampire.outputPath "artifacts/structure-function-pair.p" in
theorem structure_function_pair {α β : Type} (f g : α → β) (a b : Nat)
    (equal : (f, a) = (g, b)) (accepts : (α → β) → Prop) (positive : accepts f) : accepts g := by
  vampire [equal, positive]
#print axioms structure_function_pair

structure FunctionBundle (α β γ : Type) where
  mapping : α → β
  label : γ

-- Discover fields of a user-defined structure through its metadata.
set_option vampire.outputPath "artifacts/structure-user-defined.p" in
theorem structure_user_defined {α β γ : Type} (f g : α → β) (a b : γ)
    (equal : FunctionBundle.mk f a = FunctionBundle.mk g b)
    (accepts : (α → β) → Prop) (positive : accepts f) : accepts g := by
  vampire [equal, positive]
#print axioms structure_user_defined

set_option vampire.outputPath "artifacts/structure-nested-fields.p" in
theorem structure_nested_fields {α β : Type} (f g : α → β) (a b c d : Nat)
    (equal : ((f, a), c) = ((g, b), d))
    (accepts : (α → β) → Prop) (positive : accepts f) : accepts g := by
  vampire [equal, positive]
#print axioms structure_nested_fields

-- The explicit projection and generated constructor equation must use the
-- same symbol, including when the constructor occurs under a quantifier.
set_option vampire.outputPath "artifacts/structure-quantified-projection.p" in
theorem structure_quantified_projection (marker : Nat) (accepts : (Nat → Nat) → Prop)
    (rule : ∀ p : (Nat → Nat) × Nat, p = ((fun x => x), marker) → accepts p.1) :
    accepts (fun x => x) := by
  vampire [rule]
#print axioms structure_quantified_projection

-- Preserve native numeral literals while inspecting these constructor fields.
set_option vampire.outputPath "artifacts/structure-literal-field.p" in
theorem structure_literal_field (accepts : (Nat → Nat) → Prop)
    (rule : ∀ p : (Nat → Nat) × Nat, p = ((fun x => x), 0) → accepts p.1) :
    accepts (fun x => x) := by
  vampire [rule]
#print axioms structure_literal_field

-- Missing premises must not be supplied by the new metadata equations.
set_option vampire.outputPath "artifacts/structure-explicit-selection.p" in
example {α β : Type} (f g : α → β) (a b : Nat) (equal : (f, a) = (g, b))
    (accepts : (α → β) → Prop) (positive : accepts f) : accepts g := by
  fail_if_success vampire []
  vampire [equal, positive]

structure DependentBundle where
  carrier : Type
  value : carrier

open Lean Meta Elab Command Auto.Embedding.Lam

-- A dependent field cannot be assigned a fixed first-order result sort.
run_cmd liftTermElabM do
  let constructor ← mkAppM ``DependentBundle.mk #[mkConst ``Nat, toExpr (42 : Nat)]
  let argument : VampireHammer.Export.StructureProjections.Argument :=
    ⟨.base .nat, .base (.ncst (.natVal 42)), toExpr (42 : Nat)⟩
  let fields ← VampireHammer.Export.StructureProjections.collect
    (mkConst ``DependentBundle) constructor #[argument]
  unless fields.isEmpty do throwError "dependent field was given a fixed first-order sort"

structure VerifiedFunction (α β : Type) where
  mapping : α → β
  property : ∀ x, mapping x = mapping x

-- A dependent proof field makes Auto specialize the preceding mapping.
-- The metadata equation must recover that field from the source valuation,
-- even when it is no longer an explicit constructor-function argument.
set_option vampire.outputPath "artifacts/structure-specialized-field.p" in
theorem structure_specialized_field {α β : Type} (f g : α → β)
    (hf : ∀ x, f x = f x) (hg : ∀ x, g x = g x)
    (equal : VerifiedFunction.mk f hf = VerifiedFunction.mk g hg)
    (accepts : (α → β) → Prop) (positive : accepts f) : accepts g := by
  vampire [equal, positive, hf, hg]
#print axioms structure_specialized_field

-- Constructor equality also follows from equality of data fields. The two
-- dependent proof fields need no equality premise: Lean checks proof irrelevance.
set_option vampire.outputPath "artifacts/structure-proof-irrelevance.p" in
theorem structure_proof_irrelevance {α β : Type} (f g : α → β)
    (hf : ∀ x, f x = f x) (hg : ∀ x, g x = g x) (equal : f = g) :
    VerifiedFunction.mk f hf = VerifiedFunction.mk g hg := by
  vampire [equal, hf, hg]
#print axioms structure_proof_irrelevance

-- A subset of data fields cannot justify extensionality.
run_cmd liftTermElabM do
  let type ← Elab.Term.elabTerm
    (← `(∀ x y : (Nat → Nat) × Nat, x.1 = y.1 → x = y)) none
  if (← VampireHammer.Export.StructureProjections.proveExtensionality? type).isSome then
    throwError "partial fields incorrectly certified structure extensionality"

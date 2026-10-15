import VampireHammer
import VampireHammer.Export.LawInstances
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Set.Basic

open Lean Meta Elab Tactic

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- Validate the generated laws: each must prove its stated type through the
-- kernel, and no binder opened while walking the formula may escape into one.
elab "check_law_instances " proposition:term " expect " count:num : tactic =>
  withMainContext do
    let type ← instantiateMVars (← Term.elabTerm proposition (some (mkSort .zero)))
    let source : Auto.Lemma := ⟨⟨← mkFreshExprMVar type, type, .leaf "test source"⟩, #[]⟩
    let laws ← VampireHammer.Export.LawInstances.collect #[source]
    unless laws.size == count.getNat do
      throwError "expected {count.getNat} law-instance facts, got {laws.size}: {laws.map (·.type)}"
    for law in laws do
      let checked ← instantiateMVars (mkApp2 (mkConst ``id [.zero]) law.type law.proof)
      match Kernel.check (← getEnv) (← getLCtx) checked with
      | .ok _ => pure ()
      | .error _ => throwError "law-instance fact failed kernel checking: {law.type}"

-- Int addition contributes commutativity, associativity and both identity laws
-- for the zero that occurs in the source.
example (a : Int) : True := by
  check_law_instances (a + 0 = a) expect 4
  trivial

-- Without a unit in the source there are no identity laws to connect to.
example (a b : Int) : True := by
  check_law_instances (a * b = b * a) expect 2
  trivial

-- Multiplication by one contributes its own identity laws.
example (a : Int) : True := by
  check_law_instances (a * 1 = 1 * a) expect 4
  trivial

-- Local typeclass structure contributes laws for the local operation.
example {G : Type} [CommMagma G] (a b : G) : True := by
  check_law_instances (a * b = b * a) expect 1
  trivial

-- Registered set algebra contributes its laws through the typeclass system.
example (s t : Set Int) : True := by
  check_law_instances (s ∪ t = t ∪ s) expect 2
  trivial

-- A binder opened inside the formula must not escape into an exported law.
example (g : Int → Int → Int → Int) (a b : Int) : True := by
  check_law_instances (∀ k : Int, g k a b = g k b a) expect 0
  trivial

-- These compound goals need two laws each, so they cannot be closed by the
-- direct application of a single collected fact and exercise the exported Int
-- symbols through Vampire, replay and the kernel.
theorem intCommutativity : ∀ (a b c : Int), a + b + c = c + b + a := by
  vampire []

#print axioms intCommutativity

-- Both identity laws replayed through the new Int symbols.
theorem intAddZero (a : Int) : 0 + a = a + 0 := by
  vampire []

#print axioms intAddZero

-- Identity laws combined with associativity, replayed together.
theorem intAddZeroAround : ∀ (a b : Int), 0 + a + b = a + b + 0 := by
  vampire []

#print axioms intAddZeroAround

-- Associativity of Int multiplication.
theorem intMulAssociativity : ∀ (a b c : Int), a * (b * c) = a * b * c := by
  vampire []

#print axioms intMulAssociativity

-- Set union commutativity exported through the generic law instances.
theorem setUnionCommutativity (s t : Set Int) : s ∪ t ∪ s = s ∪ (t ∪ s) := by
  vampire []

#print axioms setUnionCommutativity

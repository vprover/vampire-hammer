import VampireHammer
import VampireHammer.Export.ConstructorFacts

open Lean Meta Elab Tactic

-- The examples below use their binders only inside terms elaborated by the
-- check tactics, which the unused-variables linter cannot see.
set_option linter.unusedVariables false

inductive TaggedValue (α : Type u) where
  | first : α → TaggedValue α
  | second : α → TaggedValue α

-- Validate the generated law before connecting it to export. The proof uses
-- noConfusion and must close over precisely the caller's context.
elab "check_constructor_laws " proposition:term : tactic => withMainContext do
  let type ← instantiateMVars (← Term.elabTerm proposition (some (mkSort .zero)))
  let source : Auto.Lemma := ⟨⟨← mkFreshExprMVar type, type, .leaf "test source"⟩, #[]⟩
  let laws ← VampireHammer.Export.ConstructorFacts.collect #[source]
  -- One injectivity law for `first`, one distinctness law for `first`/`second`.
  unless laws.size == 2 do throwError "expected two checked constructor laws, got {laws.size}: {laws.map (·.type)}"
  for law in laws do
    let checked ← instantiateMVars (mkApp2 (mkConst ``id [.zero]) law.type law.proof)
    match Kernel.check (← getEnv) (← getLCtx) checked with
    | .ok _ => pure ()
    | .error _ => throwError "constructor law failed kernel checking"

example {α : Type u} (a b : α) : True := by
  check_constructor_laws (TaggedValue.first a = TaggedValue.first b)
  trivial

inductive DependentValue where
  | mk (α : Type) (value : α)

elab "check_no_constructor_laws " proposition:term : tactic => withMainContext do
  let type ← instantiateMVars (← Term.elabTerm proposition (some (mkSort .zero)))
  let source : Auto.Lemma := ⟨⟨← mkFreshExprMVar type, type, .leaf "test source"⟩, #[]⟩
  let laws ← VampireHammer.Export.ConstructorFacts.collect #[source]
  unless laws.isEmpty do throwError "dependent constructor fields should be left to the existing encoding"

example : True := by
  check_no_constructor_laws (DependentValue.mk Nat 1 = DependentValue.mk Nat 2)
  trivial

inductive Tier where
  | low | high | floating

-- Nullary constructors have no injectivity law, but every pair is distinct.
elab "check_distinctness_laws " count:num proposition:term : tactic => withMainContext do
  let type ← instantiateMVars (← Term.elabTerm proposition (some (mkSort .zero)))
  let source : Auto.Lemma := ⟨⟨← mkFreshExprMVar type, type, .leaf "test source"⟩, #[]⟩
  let laws ← VampireHammer.Export.ConstructorFacts.collect #[source]
  unless laws.size == count.getNat do
    throwError "expected {count.getNat} distinctness laws, got {laws.size}: {laws.map (·.type)}"
  for law in laws do
    let checked ← instantiateMVars (mkApp2 (mkConst ``id [.zero]) law.type law.proof)
    match Kernel.check (← getEnv) (← getLCtx) checked with
    | .ok _ => pure ()
    | .error _ => throwError "constructor distinctness law failed kernel checking"

example (x : Tier) : True := by
  check_distinctness_laws 3 (x = Tier.low)
  trivial

-- A constructor parameter bound inside the formula must not escape into a law.
example : True := by
  check_no_constructor_laws (∀ (α : Type) (a b : α), TaggedValue.first a = TaggedValue.first b)
  trivial

-- A function producing types is also a type-valued field; accepting it
-- would trigger a monomorphization fallback and discard useful other facts.
structure TypeFamilyCarrier where
  family : Nat → Type

example (family : Nat → Type) : True := by
  check_no_constructor_laws (TypeFamilyCarrier.mk family = TypeFamilyCarrier.mk family)
  trivial

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.outputPath "artifacts/constructor-injectivity.p" in
theorem constructor_injectivity_replay {α : Type u} (a b : α) :
    TaggedValue.first a = TaggedValue.first b ↔ a = b := by
  vampire []

#print axioms constructor_injectivity_replay

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.outputPath "artifacts/constructor-distinctness.p" in
theorem constructor_distinctness_replay (x : Tier) (low : x = Tier.low) (high : x = Tier.high) :
    False := by
  vampire [low, high]

#print axioms constructor_distinctness_replay

import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option linter.unusedVariables false

-- Neither β nor γ has a Nonempty instance. Their inhabitants follow from
-- source functions applied to the existing element of α.
set_option vampire.outputPath "artifacts/domain-inhabitation-direct.p" in
theorem domain_inhabitation_direct {α β : Type} (a : α) (f : α → β) (P : β → Prop)
    (positive : ∀ y, P y) (negative : ¬P (f a)) : False := by
  vampire [positive, negative]

set_option vampire.outputPath "artifacts/domain-inhabitation-chain.p" in
theorem domain_inhabitation_chain {α β γ : Type} (a : α) (f : α → β) (g : β → γ)
    (P : γ → Prop) (positive : ∀ z, P z) (negative : ¬P (g (f a))) : False := by
  vampire [positive, negative]

set_option vampire.outputPath "artifacts/domain-inhabitation-binary.p" in
theorem domain_inhabitation_binary {α β : Type} (a : α) (f : α → Nat → β) (P : β → Prop)
    (positive : ∀ y, P y) (negative : ¬P (f a 0)) : False := by
  vampire [positive, negative]

-- A cycle of functions has no starting element, so its sorts may still be
-- empty. Opaque quantified facts must not invent a witness.
example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (positive : ∀ x, P (g (f x))) (negative : ∀ x, ¬P x) : True := by
  fail_if_success have : Nonempty α := by vampire [positive, negative]
  trivial

#print axioms domain_inhabitation_direct
#print axioms domain_inhabitation_chain
#print axioms domain_inhabitation_binary

import VampireHammer

set_option vampire.higherOrder true
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5
set_option linter.unusedVariables false

-- The source function establishes β's inhabitation through a proposition value.
theorem proposition_argument_witness {β : Type} (f : Prop → β) (P : β → Prop)
    (h : ∀ p, P (f p)) (hn : ∀ x, ¬P x) : False := by
  vampire [h, hn]

-- Constant predicates inhabit higher-order domains even when no predicate
-- value appears as a ground source symbol.
theorem predicate_argument_witness {α β : Type} (a : α)
    (f : (α → Prop) → β) (P : β → Prop)
    (h : ∀ p, P (f p)) (hn : ∀ x, ¬P x) : False := by
  vampire [h, hn]

-- Function-valued intermediate results must remain available to other functions.
theorem intermediate_function_witness {α β γ δ : Type} (a : α) (b : β)
    (f : α → β → γ) (g : (β → γ) → δ) (P : δ → Prop)
    (h : ∀ x, P (g (f x))) (hn : ∀ x, ¬P x) : False := by
  vampire [h, hn]

-- A constant function supplies a data-valued higher-order argument.
theorem constant_function_argument_witness {α β γ : Type} (a : α) (b : β)
    (f : (α → β) → γ) (P : γ → Prop)
    (h : ∀ p, P (f p)) (hn : ∀ x, ¬P x) : False := by
  vampire [h, hn]

-- A function from an empty domain supplies no value in its codomain.
example {β : Type} (f : Empty → β) (P : β → Prop)
    (h : ∀ x, P (f x)) (hn : ∀ x, ¬P x) : True := by
  fail_if_success vampire_export [h, hn]
  trivial

-- Mutually dependent functions cannot create the first atomic witness.
example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (h : ∀ x, P (g (f x))) (hn : ∀ x, ¬P x) : True := by
  fail_if_success vampire_export [h, hn]
  trivial

#print axioms proposition_argument_witness
#print axioms predicate_argument_witness
#print axioms intermediate_function_witness
#print axioms constant_function_argument_witness

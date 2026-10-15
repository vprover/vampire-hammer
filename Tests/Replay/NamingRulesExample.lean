import VampireHammer

/-!
End-to-end test for Vampire's naming and definition preprocessing:
function definitions and their unfolding, unused predicate definition
removal, general splitting, inequality splitting, and the equality proxy.
The mock proof derives one clause with each rule; the trace shows whether each
was reconstructed directly.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-naming-rules.sh"
set_option vampire.outputPath "artifacts/naming-rules.p"
set_option trace.vampire.replay true

theorem namingRules {α : Type} (a : α) (f g : α → α)
    (P Q : α → α → Prop) (U V W D E F R : α → Prop)
    (hSplit : ∀ x y z, P x y ∨ Q y z)
    (hIneq : ∀ x, f x ≠ a ∨ U x) (hIneqFlipped : ∀ x, a ≠ f x ∨ V x)
    (hProxy : ∀ x, f x = a ∨ W x)
    (hDefinition : (∀ x, g x = f (f x)) ∧ W a) (hUse : ∀ x, R (g x)) (hNotR : ¬R (f (f a)))
    (hPredicate : (∀ x, D x ↔ E x ∨ F x) ∧ W a) (hD : D a) : False := by
  vampire [hSplit, hIneq, hIneqFlipped, hProxy, hDefinition, hUse, hNotR, hPredicate, hD]

#print axioms namingRules

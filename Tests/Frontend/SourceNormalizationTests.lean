import VampireHammer
import Mathlib.Data.Set.Function

open Lean Meta Elab Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

private def assertExpansion (source expected : Expr) : MetaM Unit := do
  let normalized ← VampireHammer.SourceNormalization.normalizeType source
  let normalized ← VampireHammer.SourceNormalization.unfoldForFirstOrder normalized
  unless ← isDefEq normalized expected do
    throwError "unexpected definitional expansion: {normalized}"
  -- Definitional equality alone would also accept the original opaque syntax.
  let forbidden := #[`Set.Mem, `Set.Subset, `Set.inter, `Set.union, `Set.compl,
    `Set.diff, `Set.image, `Set.preimage, `Membership.mem, `HasSubset.Subset]
  if (normalized.find? fun e => match e with
      | .const name _ => forbidden.contains name
      | _ => false).isSome then
    throwError "set syntax remains in {normalized}"

elab "check_set_expansion " source:term " against " expected:term : tactic =>
  withMainContext do
    let source ← Term.elabTerm source none
    let expected ← Term.elabTerm expected none
    assertExpansion (← instantiateMVars source) (← instantiateMVars expected)

-- Expansions work under binders, for nested set constructors, and across sorts.
example {α β : Type} (s t : Set α) (f : α → β) (x : α) (y : β) : True := by
  check_set_expansion (s ⊆ t) against (∀ x, s x → t x)
  check_set_expansion (x ∈ (s ∪ t) \ (s ∩ t)) against
    ((s x ∨ t x) ∧ ¬(s x ∧ t x))
  check_set_expansion (∀ x, x ∈ sᶜ → x ∉ t) against (∀ x, ¬s x → ¬t x)
  check_set_expansion (y ∈ f '' s) against (∃ x, s x ∧ f x = y)
  check_set_expansion (x ∈ f ⁻¹' (f '' s)) against (∃ z, s z ∧ f z = f x)
  check_set_expansion (x ∈ ({x} : Set α)) against (x = x)
  check_set_expansion (s.Nonempty) against (∃ x, s x)
  trivial

-- A named user predicate retains its symbol rather than expanding its body.
private def userSet {α : Type} (p : α → Prop) : Set α := fun x => p x ∨ ¬p x

elab "check_user_set " source:term : tactic => withMainContext do
  let expression ← Term.elabTerm source none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let normalized ← VampireHammer.SourceNormalization.normalizeType expression
  unless (normalized.find? (·.isConstOf ``userSet)).isSome do
    throwError "user predicate was unfolded: {normalized}"

elab "check_unchanged " source:term : tactic => withMainContext do
  let expression ← Term.elabTerm source none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let normalized ← VampireHammer.SourceNormalization.normalizeType expression
  unless normalized == expression do
    throwError "ordinary order notation was changed: {normalized}"

example {α : Type} (p : α → Prop) (x : α) : True := by
  check_user_set (x ∈ userSet p)
  trivial

-- An abstract instance cannot be reduced to a concrete operation.
example {α : Type} [LE α] (a b : α) : True := by
  check_unchanged (a ≤ b)
  trivial

-- Set-valued notation must follow the actual instance, not assume subset.
example {α : Type} (s t : Set α) : True := by
  letI : LE (Set α) := ⟨fun a b => ∀ x, a x ↔ b x⟩
  check_set_expansion (s ≤ t) against (∀ x, s x ↔ t x)
  trivial

elab "check_alias_application " source:term : tactic => withMainContext do
  let expression ← Term.elabTerm source none
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let some _ ← Auto.Monomorphization.ConstInst.ofExpr? #[] #[] expression
    | throwError "alias application was not recognized"
  let type ← inferType expression.getAppFn
  let normalized ← Auto.prepReduceTypeForall type
  unless normalized.isForall do
    throwError "function alias was not exposed: {normalized}"

-- Exercise both instance collection and reifier type normalization on Set aliases.
example {α : Type} (s : Set α) (x : α) : True := by
  check_alias_application (s x)
  trivial

import VampireHammer.Backend.HigherOrderChoice

namespace VampireHammer.Backend
open Lean Meta
open Internal

theorem functionalExtensionalityInstance {α β : Sort _} [Nonempty α] (f g : α → β) :
    f (differenceWitness f g) ≠ g (differenceWitness f g) ∨ f = g := by
  classical
  by_cases equal : f = g
  · exact Or.inr equal
  · exact Or.inl (differenceWitness_spec equal)

def higherOrderDifferenceValue (type : Expr) : MetaM (Option Expr) := do
  let type ← whnfR type
  unless type.isForall && !type.bindingBody!.hasLooseBVars do return none
  let functionType := type.bindingDomain!
  let second ← whnfR type.bindingBody!
  unless ← (pure (second.isForall && !second.bindingBody!.hasLooseBVars) <&&>
      isDefEq second.bindingDomain! functionType) do return none
  let function ← whnfR functionType
  unless ← (pure (function.isForall && !function.bindingBody!.hasLooseBVars) <&&>
      isDefEq function.bindingDomain! second.bindingBody!) do return none
  try
    withLocalDeclD `extensionalityLeft functionType fun left =>
      withLocalDeclD `extensionalityRight functionType fun right => do
        let value ← mkLambdaFVars #[left, right] (← mkAppM ``differenceWitness #[left, right])
        asExpectedType value type
  catch _ => pure none

def higherOrderFunctionalExtensionality (input : RuleInput) (info : FunctionalExtensionalityInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  let some operator := input.symbols.get? info.symbol | return none
  withConfig (fun config => { config with zetaDelta := true }) do
    let some value ← higherOrderDifferenceValue (← inferType operator) | return none
    unless ← isDefEq operator value do return none
    underConclusionBinders input fun bindings target => do
      let some (_, left) := bindings.find? (·.1 == info.leftVariable) | return none
      let some (_, right) := bindings.find? (·.1 == info.rightVariable) | return none
      let type ← whnfR (← inferType left)
      unless ← (pure (type.isForall && !type.bindingBody!.hasLooseBVars) <&&>
          (do isDefEq (← inferType right) type)) do return none
      let proof ← mkAppM ``functionalExtensionalityInstance #[left, right]
      higherOrderBooleanEquivalent proof target

theorem foolExhaustivenessInstance (x : Prop) : (True = x) ∨ (False = x) := by
  classical
  by_cases h : x
  · exact Or.inl (eq_true h).symm
  · exact Or.inr (eq_false h).symm

/-- Vampire's parentless theory axiom `! [X : $o] : (X = $true | X = $false)`.
The single Boolean binder is instantiated; literal order and orientation are
checked by Boolean transport in both directions. -/
def foolExhaustiveness (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  underConclusionBinders input fun bindings target => do
    let #[(_, x)] := bindings | return none
    unless ← isDefEq (← inferType x) (mkSort .zero) do return none
    higherOrderBooleanEquivalent (mkApp (mkConst ``foolExhaustivenessInstance) x) target

theorem foolDistinctnessInstance : True ≠ False := fun h => h ▸ trivial

/-- Vampire's parentless theory axiom `$true != $false`. -/
def foolDistinctness (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  underConclusionBinders input fun bindings target => do
    unless bindings.isEmpty do return none
    higherOrderBooleanEquivalent (mkConst ``foolDistinctnessInstance) target

end VampireHammer.Backend

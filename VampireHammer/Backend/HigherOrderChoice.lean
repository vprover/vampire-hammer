import VampireHammer.Backend.HigherOrderQuantifier

namespace VampireHammer.Backend
open Lean Meta
open Internal

theorem hilbertChoiceInstance {α : Sort _} [Nonempty α] (predicate : α → Prop) (x : α) :
    (predicate x = False) ∨ (predicate (quantifierWitness predicate) = True) := by
  classical
  by_cases h : predicate x
  · exact Or.inr ((fool_eq_true _).mpr (quantifierWitness_spec predicate ⟨x, h⟩))
  · exact Or.inl ((fool_eq_false _).mpr h)

/-- A choice operator has the checked value `fun P => epsilon P`. Inferring
this value from its type is allowed only at a certified fresh introduction. -/
def higherOrderChoiceValue (type : Expr) : MetaM (Option Expr) := do
  let type ← whnfR type
  unless type.isForall && !type.bindingBody!.hasLooseBVars do return none
  let predicateType ← whnfR type.bindingDomain!
  unless ← (pure (predicateType.isForall && !predicateType.bindingBody!.hasLooseBVars) <&&>
      isDefEq predicateType.bindingBody! (mkSort .zero) <&&>
      isDefEq predicateType.bindingDomain! type.bindingBody!) do return none
  try
    withLocalDeclD `choicePredicate predicateType fun predicate => do
      let value ← mkLambdaFVars #[predicate] (← mkAppM ``quantifierWitness #[predicate])
      asExpectedType value type
  catch _ => pure none

theorem choiceDefinitionInstance {α : Sort _} {choice : (α → Prop) → α}
    (definition : ∀ (predicate : α → Prop) x, predicate x → predicate (choice predicate))
    (predicate : α → Prop) (x : α) :
    (predicate x = False) ∨ (predicate (choice predicate) = True) := by
  classical
  by_cases h : predicate x
  · exact Or.inr ((fool_eq_true _).mpr (definition predicate x h))
  · exact Or.inl ((fool_eq_false _).mpr h)

theorem choiceDefinition_of_swapped {α : Sort _} {choice : (α → Prop) → α}
    (h : ∀ x (predicate : α → Prop), predicate x → predicate (choice predicate)) :
    ∀ (predicate : α → Prop) x, predicate x → predicate (choice predicate) :=
  fun predicate x => h x predicate

theorem choiceDefinition_of_exists {α : Sort _} {choice : (α → Prop) → α}
    (h : ∀ predicate : α → Prop, (∃ x, predicate x) → predicate (choice predicate)) :
    ∀ (predicate : α → Prop) x, predicate x → predicate (choice predicate) :=
  fun predicate x hx => h predicate ⟨x, hx⟩

theorem choiceDefinition_of_or {α : Sort _} {choice : (α → Prop) → α}
    (h : ∀ (predicate : α → Prop) x, ¬predicate x ∨ predicate (choice predicate)) :
    ∀ (predicate : α → Prop) x, predicate x → predicate (choice predicate) :=
  fun predicate x hx => (h predicate x).resolve_left (not_not_intro hx)

theorem choiceDefinition_of_or_swapped {α : Sort _} {choice : (α → Prop) → α}
    (h : ∀ (predicate : α → Prop) x, predicate (choice predicate) ∨ ¬predicate x) :
    ∀ (predicate : α → Prop) x, predicate x → predicate (choice predicate) :=
  fun predicate x hx => (h predicate x).resolve_right (not_not_intro hx)

/-- With `--choice_reasoning`, Vampire recognizes an input symbol as a choice
operator from a clause `~P x | P (c P)` and deletes that clause without
linking it. Recover the definition from an exported source fact of one of
the common shapes; the operator itself stays uninterpreted. -/
private def choiceDefinition? (input : RuleInput) (operator : Expr) : MetaM (Option Expr) := do
  let operatorType ← whnfR (← inferType operator)
  unless operatorType.isForall && !operatorType.bindingBody!.hasLooseBVars do return none
  let predicateType := operatorType.bindingDomain!
  let element := operatorType.bindingBody!
  let expected ← withLocalDeclD `predicate predicateType fun predicate =>
    withLocalDeclD `x element fun x => do
      let conclusion := mkApp predicate (mkApp operator predicate)
      mkForallFVars #[predicate, x] (← mkArrow (mkApp predicate x) conclusion)
  for source in input.sourceFVars do
    let source := mkFVar source
    for convert in [none, some ``choiceDefinition_of_swapped, some ``choiceDefinition_of_exists,
        some ``choiceDefinition_of_or, some ``choiceDefinition_of_or_swapped] do
      let candidate ← try
          match convert with
          | none => pure source
          | some lemma => mkAppOptM lemma #[none, some operator, some source]
        catch _ => continue
      if ← withNewMCtxDepth (isDefEq (← inferType candidate) expected) then
        return some candidate
  return none

/-- Prove only an instance of an interpreted choice operator, or of an input
symbol whose exported choice definition is found among the source facts.
No parent proof or arbitrary function of the right type is used. -/
def higherOrderChoice (input : RuleInput) (info : ChoiceAxiomInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  let some operator := input.symbols.get? info.symbol | return none
  withConfig (fun config => { config with zetaDelta := true }) do
    let interpreted ← match ← higherOrderChoiceValue (← inferType operator) with
      | some value => isDefEq operator value
      | none => pure false
    let definition? ← if interpreted then pure none else choiceDefinition? input operator
    unless interpreted || definition?.isSome do return none
    underConclusionBinders input fun bindings target => do
      let some (_, argument) := bindings.find? (·.1 == info.variableName) | return none
      let some terms ← materializeInferenceTerms input #[] bindings #[info.predicate] | return none
      let some predicate := terms[0]? | return none
      let type ← whnfR (← inferType predicate)
      unless ← (pure (type.isForall && !type.bindingBody!.hasLooseBVars) <&&>
          isDefEq type.bindingBody! (mkSort .zero) <&&>
          (do isDefEq type.bindingDomain! (← inferType argument))) do return none
      let proof ← match definition? with
        | some definition => mkAppM ``choiceDefinitionInstance #[definition, predicate, argument]
        | none => mkAppM ``hilbertChoiceInstance #[predicate, argument]
      higherOrderBooleanEquivalent proof target

end VampireHammer.Backend

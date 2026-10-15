import VampireHammer
import Mathlib.Data.List.Basic

open Lean Meta Elab Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace AttributeLemmaTests

-- These scalar definitions remain opaque to the automatic unfolding pass.
private def advance (n : Nat) : Nat := n + 1
@[simp] private theorem advance_zero : advance 0 = 1 := rfl
private def aliasBase (n : Nat) : Nat := n + 2
private abbrev aliasOperation (n : Nat) : Nat := aliasBase n
@[simp] private theorem alias_operation_zero : aliasOperation 0 = 2 := rfl
private def marked (n : Nat) : Prop := n = 0
@[grind →] private theorem marked_elim (n : Nat) (h : marked n) : n = 0 := h

private def middle (n : Nat) : Nat := n + 3
private def outer (n : Nat) : Nat := middle n
@[simp] private theorem outer_eq (n : Nat) : outer n = middle n := rfl
@[simp] private theorem middle_zero : middle 0 = 3 := rfl

-- No theorem attribute supplies the meaning of this operation.
private def untagged (n : Nat) : Nat := n + 5

private opaque noisy : Nat → Prop

-- A crowded grind bucket with no applicable fact must leave room to discover
-- an unrelated, useful simp fact at a later term in the same source problem.
elab "populate_selection_noise" : command => do
  for index in [:160] do
    let name := mkIdent (Name.mkSimple s!"selection_noise_{index}")
    let numeral : TSyntax `term := ⟨Syntax.mkNumLit s!"{index + 1}"⟩
    Elab.Command.elabCommand (← `(command|
      @[grind →] theorem $name : noisy $numeral → True := by intro _; trivial))

populate_selection_noise

-- Check discovery directly so a passing example cannot mask missing selection.
elab "check_selected " source:term " using " declaration:ident : tactic => withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let expected ← realizeGlobalConstNoOverloadWithInfo declaration
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.AttributeLemmas.collect #[fact]
    unless selected.all (fun fact => !fact.proof.hasMVar && !fact.type.hasMVar) do
      throwError "selected fact contains unresolved metavariables"
    unless selected.any (fun fact => (fact.proof.find? (·.isConstOf expected)).isSome) do
      throwError "did not select {expected} for {expression}"

elab "check_excluded " source:term " excluding " declaration:ident : tactic => withMainContext do
  let expression ← Term.elabTerm source (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let excluded ← realizeGlobalConstNoOverloadWithInfo declaration
  withLocalDeclD `testFact expression fun hypothesis => do
    let fact : Auto.Lemma := ⟨⟨hypothesis, expression, .leaf "test"⟩, #[]⟩
    let selected ← VampireHammer.AttributeLemmas.collect #[fact] (some excluded)
    if selected.isEmpty || selected.any (fun fact =>
        (fact.proof.find? (·.isConstOf excluded)).isSome) then
      throwError "excluded theorem was selected, or unrelated discovery stopped"

example : True := by
  check_selected (advance 0 = 1) using advance_zero
  check_selected (aliasBase 0 = 2) using alias_operation_zero
  check_selected (noisy 0 ∧ aliasBase 0 = 2) using alias_operation_zero
  trivial

-- The useful second lemma is indexed at a term absent from the source goal.
-- Discovery follows the checked first lemma's conclusion, without unfolding
-- every scalar definition or increasing the total premise limit.
set_option vampire.attributeLemmaRounds 2 in
example : True := by
  check_selected (outer 0 = 3) using outer_eq
  check_selected (outer 0 = 3) using middle_zero
  check_excluded (outer 0 = 3) excluding middle_zero
  trivial

set_option vampire.attributeLemmaRounds 1 in
example : True := by
  fail_if_success check_selected (outer 0 = 3) using middle_zero
  trivial

set_option vampire.attributeLemmaLimit 1 in
set_option vampire.attributeLemmaRounds 2 in
example : True := by
  fail_if_success check_selected (outer 0 = 3) using middle_zero
  trivial

example (n : Nat) : True := by
  check_selected (marked n) using marked_elim
  trivial

-- Selection must find indexed facts at terms beneath quantifiers, and return
-- closed universal instances rather than leaking temporary metavariables.
example : True := by
  check_selected (∀ n : Nat, marked n → n = 0) using marked_elim
  trivial

-- Available mathlib simp lemmas are instantiated at the concrete list type.
example : True := by
  check_selected (([] : List Nat).length = 0) using List.length_nil
  trivial

set_option vampire.outputPath "artifacts/attribute-lemmas/simp.p" in
theorem simp_discovery : advance 0 = 1 ∨ advance 0 = 2 := by
  vampire []

set_option vampire.outputPath "artifacts/attribute-lemmas/alias.p" in
theorem alias_discovery : aliasBase 0 = 2 ∨ aliasBase 0 = 3 := by
  vampire []

set_option vampire.outputPath "artifacts/attribute-lemmas/grind.p" in
theorem grind_discovery (n : Nat) (h : marked n) : n = 0 ∨ n = 1 := by
  vampire [h]

set_option vampire.outputPath "artifacts/attribute-lemmas/list.p" in
theorem list_discovery : ([] : List Nat).length = 0 ∨ ([] : List Nat).length = 1 := by
  vampire []

#print axioms simp_discovery
#print axioms alias_discovery
#print axioms grind_discovery
#print axioms list_discovery

set_option vampire.outputPath "artifacts/attribute-lemmas/chained.p" in
set_option vampire.attributeLemmaRounds 2 in
theorem chained_discovery : outer 0 = 3 ∨ outer 0 = 4 := by
  vampire []
#print axioms chained_discovery

set_option vampire.definitionLemmas true in
set_option vampire.outputPath "artifacts/attribute-lemmas/definition.p" in
theorem definition_discovery : untagged 0 = 5 ∨ untagged 0 = 6 := by
  vampire []
#print axioms definition_discovery

end AttributeLemmaTests

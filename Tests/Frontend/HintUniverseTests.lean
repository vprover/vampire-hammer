import VampireHammer

open Lean Meta Elab Tactic

namespace HintUniverseTests

-- These defaults must not run while collecting an unconstrained premise.
theorem proofTheorem {α : Type u} (_a : α)
    (_unused : True := by fail "premise default unexpectedly executed") : True := True.intro

set_option linter.defProp false in
def proofDefinition {α : Type u} (_a : α)
    (_unused : True := by fail "premise default unexpectedly executed") : True := True.intro

set_option vampire.attributeLemmas false
set_option vampire.alignNestedDefinitions false

elab "check_polymorphic_hints " hints:Auto.hints : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  withLocalDeclD `negative (mkApp (mkConst ``Not) target) fun negative => do
    let (facts, _) ← VampireHammer.Export.Internal.collectFactsWithTypeclassLaws
      hints #[] #[] negative.fvarId!
    for name in #[``proofTheorem, ``proofDefinition] do
      let some fact := facts.find? (fun fact => fact.proof.isConstOf name)
        | throwError "bare proof hint did not preserve the complete constant {name}"
      unless fact.type.isForall && !fact.params.isEmpty && !fact.proof.hasMVar && !fact.type.hasMVar do
        throwError "bare proof hint has invalid polymorphic binders or metavariables"

example : True := by
  check_polymorphic_hints [proofTheorem, proofDefinition]
  exact True.intro

-- Applied terms and local hints still elaborate normally. In particular a
-- local hypothesis shadowing the global definition must stay local.
example (proofDefinition : False) : False := by
  vampire [proofDefinition]

example : True := by
  vampire [proofTheorem (α := Nat) 0 True.intro, proofDefinition (α := Nat) 0 True.intro]

end HintUniverseTests

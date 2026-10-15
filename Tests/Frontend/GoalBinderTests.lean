import VampireHammer

set_option vampire.attributeLemmas false
set_option vampire.timeLimit 2

namespace GoalBinderTests

-- A scalar record argument keeps the interface predicate first order. Its
-- defining universal must nevertheless remain connected to its positive facts
-- when the goal introduces an element of the potentially empty carrier.
structure Domain where
  carrier : Type
  predicate : carrier → Prop

private def Universal (domain : Domain) : Prop := ∀ x, domain.predicate x
private def UniversalAlias (domain : Domain) : Prop := Universal domain

class Certified (domain : Domain) : Prop where
  law : Universal domain

set_option vampire.outputPath "artifacts/goal-binders/class-law.p" in
theorem class_law (domain : Domain) [Certified domain] : Universal domain := by
  vampire []

set_option vampire.outputPath "artifacts/goal-binders/alias.p" in
theorem alias_law (domain : Domain) [Certified domain] : UniversalAlias domain := by
  vampire []

set_option vampire.outputPath "artifacts/goal-binders/hint.p" in
theorem explicit_law (domain : Domain) (h : Universal domain) : UniversalAlias domain := by
  fail_if_success vampire []
  vampire [h]

set_option vampire.outputPath "artifacts/goal-binders/empty.p" in
example (domain : Domain) [Certified domain] : True := by
  fail_if_success have : Nonempty domain.carrier := by vampire []
  trivial

set_option vampire.outputPath "artifacts/goal-binders/observational.p" in
example (domain : Domain) [Certified domain] : UniversalAlias domain := by
  vampire_export []
  exact Certified.law

-- Nested alignment adds expanded copies of selected facts, retaining their
-- opaque interface forms. Disable decomposition to exercise this export path.
set_option vampire.decomposeGoals false in
set_option vampire.alignNestedDefinitions true in
set_option vampire.outputPath "artifacts/goal-binders/nested.p" in
theorem nested_law (domain : Domain) (q : Prop) (h : Universal domain) (hq : q) :
    UniversalAlias domain ∧ q := by
  vampire [h, hq]

set_option vampire.decomposeGoals false in
set_option vampire.alignNestedDefinitions true in
example (domain : Domain) (q : Prop) (h : Universal domain) (hq : q) : True := by
  fail_if_success have : UniversalAlias domain ∧ q := by vampire [hq]
  trivial

private def Connected (domain : Domain) (a b : domain.carrier) : Prop :=
  domain.predicate a → domain.predicate b

set_option vampire.decomposeGoals false in
set_option vampire.outputPath "artifacts/goal-binders/nested-chain.p" in
theorem nested_chain (domain : Domain) (a b c : domain.carrier) (q : Prop)
    (ab : Connected domain a b) (bc : Connected domain b c) (hq : q) :
    Connected domain a c ∧ q := by
  fail_if_success vampire [ab, bc, hq] (alignNestedDefinitions := false)
  vampire [ab, bc, hq]

#print axioms class_law
#print axioms alias_law
#print axioms explicit_law

end GoalBinderTests

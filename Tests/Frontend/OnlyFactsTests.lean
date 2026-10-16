import VampireHammer

open Lean Meta Elab Tactic

namespace OnlyFactsTests

set_option vampire.executable "/missing-vampire-only-tests"

class Laws (α : Type) extends Mul α, One α where
  identity (x : α) : 1 * x = x
  associative (x y z : α) : (x * y) * z = x * (y * z)

-- Class laws are available to ordinary vampire, but never to vampire only.
example [Laws α] (x : α) : 1 * x = x := by
  vampire []
  -- Populate the cache before the restricted call in the next example.

example [Laws α] (x : α) : 1 * x = x := by
  fail_if_success vampire only []
  fail_if_success vampire only (onlyFacts := false) (decomposeGoals := true) []
  vampire only [Laws.identity]

example [Laws α] (a b c d : α) : (b * c) * d = b * (c * d) := by
  fail_if_success vampire only [Laws.associative a]
  vampire only [Laws.associative]

opaque P : Nat → Prop
@[simp] axiom registered : P 0

example : P 0 := by vampire []

example : P 0 := by
  fail_if_success vampire only []
  vampire only [registered]

example (p : Prop) (h : p) : p := by
  fail_if_success vampire only
  fail_if_success vampire only []
  vampire only [h]

example (p : Prop) (h : p) : p := by vampire only [*]
example (p : Prop) : p → p := by vampire only
example (p q : Prop) (h : p) (step : p → q) : q := by
  vampire only (timeout := 1) [h, step] (quiet := true)

-- Datatype and Boolean facts must not leak through direct closure either.
example : true ≠ false := by
  fail_if_success vampire only []
  vampire only [show true ≠ false from fun h => Bool.noConfusion h]

example (h : true = false) : False := by
  fail_if_success vampire only [h]
  exact Bool.noConfusion h

-- Inspect the actual collection, with all discovery switches enabled.
-- The sole source proposition must be the required negated goal.
elab "check_only_collection" : tactic => withMainContext do
  let target ← (← getMainGoal).getType
  withLocalDeclD `negative (mkApp (mkConst ``Not) target) fun negative => do
    let hints ← `(Auto.hints| [])
    withOptions (fun options => options.set `vampire.onlyFacts true
        |>.set `vampire.attributeLemmas true |>.set `vampire.siblingLemmas true
        |>.set `vampire.suggestedLemmas 16) do
      let (facts, _) ← VampireHammer.Export.Internal.collectFactsWithTypeclassLaws
        hints #[] #[] negative.fvarId!
      unless facts.size == 1 && facts[0]!.proof == negative do
        throwError "unexpected automatic facts: {facts.map (·.deriv)}"

example [Laws α] (x : α) : 1 * x = x := by
  check_only_collection
  exact Laws.identity x

-- Real export, search and kernel replay, with direct closure disabled.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.directProof false in
set_option vampire.portfolioCores 1 in
example (p q r : Prop) (h : p) (pq : p → q) (qr : q → r) : r := by
  vampire only [h, pq, qr]

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.directProof false in
set_option vampire.cache false in
set_option vampire.portfolioCores 1 in
example (p q r : Prop) (h : p) (pq : p → q) (qr : q → r) : r := by
  vampire only (parallel := false) (routedSlices := false)
    (higherOrder := false) [h, pq, qr]

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.directProof false in
set_option vampire.cache false in
example (p q r : Prop) (h : p) (pq : p → q) (qr : q → r) : r := by
  vampire only (parallel := false) (routedSlices := false)
    (higherOrder := true) [h, pq, qr]

-- Export supports the same restriction and does not solve the goal.
set_option vampire.outputPath "artifacts/only-facts.p" in
example [Laws α] (x : α) : 1 * x = x := by
  vampire_export only []
  exact Laws.identity x

end OnlyFactsTests

import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

-- Exercise the single-route protocol independently of the default sliced search.
set_option vampire.routedSlices false

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback true
-- This file verifies the native-to-FO protocol, independently of the native
-- strategy retry covered by HigherOrderSearchRetryTests.
set_option vampire.higherOrderSearchRetry false
set_option linter.unusedVariables false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.timeLimit 5
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- The function space is inhabited by q even when α is empty. Native THF
-- requires a witness for α; the checked object encoding does not (nor does
-- the tactic's deferred inhabitant, disabled here).
example {α : Type} (q : α → Prop) (P : (α → Prop) → Prop) (Q : Prop)
    (h : ∀ f, P f → Q) (hp : P q) : Q := by
  fail_if_success vampire [h, hp] (higherOrderFallback := false) (directProof := false)
    (deferInhabitants := false)
  exact h q hp

set_option vampire.outputPath "artifacts/ho-fallback-empty-domain.p" in
theorem fallback_empty_domain {α : Type} (q : α → Prop)
    (P : (α → Prop) → Prop) (Q : Prop) (h : ∀ f, P f → Q) (hp : P q) : Q := by
  vampire [h, hp] (directProof := false) (deferInhabitants := false)

#eval show IO Unit from do
  let text ← IO.FS.readFile "artifacts/ho-fallback-empty-domain.p"
  unless text.contains "tff(" && !text.contains "thf(" do
    throw <| IO.userError "missing-domain failure did not reach first-order export"

-- With the deferred inhabitant available, the tactic's own recovery repairs the
-- missing domain natively; the fallback must not preempt it with a first-order retry.
set_option vampire.outputPath "artifacts/ho-fallback-deferred-domain.p" in
theorem fallback_deferred_domain {α : Type} (q : α → Prop)
    (P : (α → Prop) → Prop) (Q : Prop) (h : ∀ f, P f → Q) (hp : P q) : Q := by
  vampire [h, hp] (directProof := false)

#eval show IO Unit from do
  let text ← IO.FS.readFile "artifacts/ho-fallback-deferred-domain.p"
  unless text.contains "thf(" && !text.contains "tff(" do
    throw <| IO.userError "fallback preempted the deferred inhabitant recovery"

set_option vampire.executable "Tests/testdata/scripts/mock-ho-first-order-fallback.py"

-- An unsuccessful native search also retries, retaining its artifacts.
set_option vampire.outputPath "artifacts/ho-fallback-search.p" in
theorem fallback_search (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp] (directProof := false)

#eval show IO Unit from do
  let native ← IO.FS.readFile "artifacts/ho-fallback-search.p.higher-order"
  let current ← IO.FS.readFile "artifacts/ho-fallback-search.p"
  let output ← IO.FS.readFile "artifacts/ho-fallback-search.p.higher-order.stdout"
  unless native.contains "thf(" && current.contains "tff(" && output.contains "GaveUp" &&
      output.contains "native search limit: 3" do
    throw <| IO.userError "fallback did not retain the native search artifacts"

-- Timeout handling leaves a first-order attempt, and clears the native-only
-- strategy before invoking the real first-order portfolio.
set_option vampire.outputPath "artifacts/ho-fallback-timeout.p" in
set_option vampire.strategy "test-timeout" in
theorem fallback_timeout (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp] (directProof := false)

#eval show IO Unit from do
  let output ← IO.FS.readFile "artifacts/ho-fallback-timeout.p.higher-order.stdout"
  unless output.contains "Timeout" do
    throw <| IO.userError "timeout did not reach the first-order retry"

example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  fail_if_success vampire [h, hp] (higherOrderFallback := false) (directProof := false)
  exact h 0 hp

-- The first-order retry must not manufacture inhabitants of empty domains.
example {α β : Type} (f : α → β) (g : β → α) (P : α → Prop)
    (h : ∀ x, P (g (f x))) (hn : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [h, hn]
  trivial

#print axioms fallback_empty_domain
#print axioms fallback_search
#print axioms fallback_timeout

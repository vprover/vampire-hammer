import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.outputPath "artifacts/bool-bridge.p"
set_option vampire.timeLimit 10
set_option Elab.async false
-- Exercise the prover rather than the direct application of a premise.
set_option vampire.directProof false

/-! `Bool` is an uninterpreted sort with symbols for its constants and
operations. lean-auto's checked `boolFacts`, `Bool.eq_false_or_eq_true` and
`decide_eq_true_eq` state their meaning; replay maps the symbols back. -/

example {p : Prop} [Decidable p] : decide p = false → ¬p := by vampire
example {p : Prop} [Decidable p] (h : decide p = true) : p := by vampire
example (b c : Bool) (h : (b && c) = true) : b = true := by vampire
example (b : Bool) (h : (!b) = true) : b = false := by vampire
example (b c : Bool) (h : b = true ∨ c = true) : (b || c) = true := by vampire

-- The encoding must not identify an arbitrary `Bool` with `true`.
example (b : Bool) : b = true ∨ b = false := by
  fail_if_success have : b = true := by vampire
  cases b <;> simp

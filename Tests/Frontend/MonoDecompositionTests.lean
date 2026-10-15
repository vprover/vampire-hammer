import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

-- Exercise the single-route protocol independently of the default sliced search.
set_option vampire.routedSlices false

open Lean Elab Command

set_option vampire.monoHeartbeats 1
set_option vampire.directProof false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.timeLimit 4
set_option vampire.executable "Tests/testdata/scripts/mock-mono-decomposition.py"

run_cmd do
  IO.FS.createDirAll "artifacts/goal-decomposition"
  IO.FS.writeFile "artifacts/goal-decomposition/mono.calls" ""

-- FO hits its tiny mono window. Constructor branches close from selected
-- facts before any HO search; the mock cannot prove these goals.
theorem mono_decomposition (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  vampire [p, q]

example (P Q R : Prop) (p : P) (q : Q) (r : R) : (P ∧ Q) ∧ R := by
  constructor
  · vampire [p, q]
  · exact r

-- Exercise the plain slice with suggestions configured, too.
set_option vampire.suggestedLemmas 1 in
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  vampire [p, q]

run_cmd do
  unless (← IO.FS.readFile "artifacts/goal-decomposition/mono.calls").isEmpty do
    throwError "HO search ran before successful mono decomposition"

-- Missing selected facts force rollback and exactly one original-goal HO
-- attempt. No branch starts HO and no late fallback restarts the FO tree.
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  fail_if_success vampire [p]
  exact ⟨p, q⟩

run_cmd do
  unless (← IO.FS.readFile "artifacts/goal-decomposition/mono.calls") == "ho\n" do
    throwError "mono decomposition retried branches in HO or used an unselected fact"
  IO.FS.writeFile "artifacts/goal-decomposition/mono.calls" ""

-- Disabling decomposition retains the existing direct mono-to-HO fallback.
set_option vampire.decomposeGoals false in
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  fail_if_success vampire [p, q]
  exact ⟨p, q⟩

run_cmd do
  unless (← IO.FS.readFile "artifacts/goal-decomposition/mono.calls") == "ho\n" do
    throwError "disabled decomposition changed the mono-to-HO route"
  IO.FS.writeFile "artifacts/goal-decomposition/mono.calls" ""

-- The ablation switch retains the old order: HO is attempted first, and
-- ordinary late decomposition can still finish after the mock HO fails.
set_option vampire.monoDecomposition false in
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  vampire [p, q]

run_cmd do
  unless (← IO.FS.readFile "artifacts/goal-decomposition/mono.calls") == "ho\n" do
    throwError "monoDecomposition=false did not retain the earlier fallback order"

-- If a structural branch also exhausts the tiny shared mono allowance, the
-- real prover must replay a proof of the restored original conjunction in HO.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.outputPath "artifacts/goal-decomposition/mono-ho.p" in
theorem mono_decomposition_ho (α : Type) (R : α → α → Prop) (a b c d : α)
    (trans : ∀ x y z, R x y → R y z → R x z)
    (ab : R a b) (bc : R b c) (cd : R c d) : R a d ∧ R a b := by
  vampire [trans, ab, bc, cd]

run_cmd do
  let text ← IO.FS.readFile "artifacts/goal-decomposition/mono-ho.p"
  unless text.contains "thf(" do
    throwError "failed mono decomposition did not replay the original goal in HO"

-- The default zero setting still uses the ordinary FO route.
set_option vampire.monoHeartbeats 0 in
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.outputPath "artifacts/goal-decomposition/mono-disabled.p" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

run_cmd do
  let text ← IO.FS.readFile "artifacts/goal-decomposition/mono-disabled.p"
  unless text.contains "tff(" && !text.contains "thf(" do
    throwError "disabled mono window changed the ordinary FO route"

#print axioms mono_decomposition
#print axioms mono_decomposition_ho

import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

set_option vampire.higherOrder true
set_option vampire.attributeLemmas false
set_option vampire.outputPath "artifacts/higher-order-export.p"

example (i : Type) (a b : i) (p : i → Prop)
    (all : ∀ F : i → i, p (F a)) (neg : ¬p b) : False := by
  vampire_export [all, neg]
  exact neg (all (fun _ => b))

#eval show IO Unit from do
  let text ← IO.FS.readFile "artifacts/higher-order-export.p"
  unless text.contains "thf(" && text.contains " @ " && text.contains " > " do
    throw (IO.userError "native higher-order option did not reach THF export")

set_option vampire.executable "Tests/testdata/scripts/mock-higher-order.sh"
set_option vampire.outputPath "artifacts/higher-order-pipeline.p"
set_option trace.vampire.replay true

theorem mocked_higher_order_pipeline (i : Type) (a b : i) (p : i → Prop)
    (all : ∀ F : i → i, p (F a)) (neg : ¬p b) : False := by
  vampire [all, neg]

#eval show IO Unit from do
  let text ← IO.FS.readFile "artifacts/higher-order-pipeline.p.stdout"
  unless text.contains "constrained_superposition,[unifier" do
    throw (IO.userError "mocked higher-order proof did not reach the capture pipeline")

#print axioms mocked_higher_order_pipeline

set_option vampire.executable "Tests/testdata/scripts/mock-higher-order-choice.sh"
set_option vampire.outputPath "artifacts/higher-order-choice-pipeline.p"

theorem mocked_choice_pipeline (i : Type) (a : i) (p : (i → i) → Prop)
    (ex : (∃ F, p F) = True) (neg : ∀ F, ¬p F) : False := by
  vampire [ex, neg]

#print axioms mocked_choice_pipeline

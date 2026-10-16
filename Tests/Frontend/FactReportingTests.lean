import VampireHammer

open Lean Meta Elab Tactic

namespace FactReportingTests

set_option vampire.executable "/missing-vampire-fact-reporting-tests"

class Laws (α : Type) extends Mul α, One α where
  identity (x : α) : 1 * x = x
  associative (x y z : α) : (x * y) * z = x * (y * z)

elab "check_fact_report " expected:str " excluding " excluded:str " in " action:tacticSeq : tactic => do
  let before := (← Core.getMessageLog).toList.length
  evalTactic action
  let messages := (← Core.getMessageLog).toList.drop before
  let text := String.intercalate "\n" (← messages.mapM (fun message => message.data.toString))
  unless text.contains expected.getString do
    throwError "missing report {expected.getString}: {text}"
  if text.contains excluded.getString then
    throwError "unexpected report {excluded.getString}: {text}"

-- Only the used identity law is reported, not the collected associativity law.
example [inst : Laws α] (x : α) : 1 * x = x := by
  check_fact_report "vampire only [Laws.identity]" excluding "associative" in
    vampire []

-- Same goal and hints: exercise cached proof provenance.
example [inst : Laws α] (x : α) : 1 * x = x := by
  check_fact_report "vampire only [Laws.identity]" excluding "associative" in
    vampire []

example [inst : Laws α] (x : α) : 1 * x = x := by
  check_fact_report "" excluding "vampire used additional facts" in
    vampire (reportFacts := false) []

example [inst : Laws α] (x : α) : 1 * x = x := by
  check_fact_report "" excluding "vampire used additional facts" in
    vampire only [Laws.identity]

example (p : Prop) (h : p) : p := by
  check_fact_report "" excluding "vampire used additional facts" in
    vampire [h]

-- Collecting automatic facts is not enough to trigger a report.
example [inst : Laws α] (x : α) (h : 1 * x = x) : 1 * x = x := by
  check_fact_report "" excluding "vampire used additional facts" in
    vampire [h]

opaque P : Nat → Prop
@[simp] axiom registered : P 0

example : P 0 := by
  check_fact_report "vampire only [registered]" excluding "Laws" in vampire []

-- Provenance must also survive external search and checked replay.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
set_option vampire.directProof false in
set_option vampire.cache false in
set_option vampire.portfolioCores 1 in
example [inst : Laws α] (x : α) : 1 * x = x := by
  check_fact_report "[Laws.identity]" excluding "associative" in
    vampire []

-- Inspect a marker under a binder; its statement must retain readable names.
example : True := by
  run_tac do
    let marked ← withLocalDeclD `x (mkConst ``Nat) fun x => do
      let type ← mkEq x x
      let fact : Auto.Lemma := ⟨⟨← mkEqRefl x, type, .leaf "test equality"⟩, #[]⟩
      mkLambdaFVars #[x] (VampireHammer.FactReporting.markLemma fact).proof
    let facts ← VampireHammer.FactReporting.usedFacts marked
    unless facts.size == 1 && facts[0]!.1.contains "x = x" do
      throwError "incorrect binder provenance: {facts}"
  trivial

end FactReportingTests

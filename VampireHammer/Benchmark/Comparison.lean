import VampireHammer.Benchmark.Mathlib
import Duper
import Aesop

/-! Tactic baselines share the declaration-time environment, explicit premise
names, local hypotheses, kernel check and dependency audit with VampireHammer.
The runner enforces wall-clock limits; heartbeat limits are disabled. -/

namespace VampireHammer.Benchmark
open Lean Elab Term

initialize registerBenchmarkTactic "duper" fun premises => do
  let terms : Array Term := premises.map fun name => ⟨mkIdent name⟩
  `(term| by intros; duper [*, $[$terms],*])

initialize registerBenchmarkTactic "simp_all" fun premises => do
  let terms : Array Term := premises.map fun name => ⟨mkIdent name⟩
  `(term| by intros; simp_all [$[$terms:term],*])

initialize registerBenchmarkTactic "aesop" fun premises => do
  let clauses ← premises.mapM fun name => do
    let ident := mkIdent name
    `(Aesop.tactic_clause| (add unsafe $ident:ident))
  let config ← `(Aesop.tactic_clause| (config := {
    maxRuleApplications := 0, maxRuleApplicationDepth := 0,
    -- This Aesop revision treats zero as immediate exhaustion for this
    -- field, despite its documentation. Leave the wall watchdog in charge.
    maxNormIterations := 1000000000, maxSafePrefixRuleApplications := 0 }))
  let clauses := #[config] ++ clauses
  `(term| by intros; aesop $[$clauses]*)

initialize registerBenchmarkTactic "grind" fun premises => do
  let terms : Array Term := premises.map fun name => ⟨mkIdent name⟩
  `(term| by intros; grind [$[$terms:term],*])

end VampireHammer.Benchmark

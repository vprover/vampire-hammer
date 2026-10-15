import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

set_option vampire.higherOrder true
set_option vampire.higherOrderFallback false
set_option vampire.directProof false
set_option vampire.decomposeGoals false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

-- The solver treats scalar operations as uninterpreted; replay still uses
-- their actual Lean meaning. These need no new string/bitvector axioms.
set_option vampire.outputPath "artifacts/ho-string-scalar.p" in
theorem string_scalar_replay (P : Nat → Prop) (s : String) (h : P s.length) : P s.length := by
  vampire [h]

set_option vampire.outputPath "artifacts/ho-bv-scalar.p" in
theorem bitvector_scalar_replay (P : BitVec 4 → Prop) (x : BitVec 4) (h : P (x + 1)) : P (x + 1) := by
  vampire [h]

#eval show IO Unit from do
  let strings ← IO.FS.readFile "artifacts/ho-string-scalar.p"
  let bits ← IO.FS.readFile "artifacts/ho-bv-scalar.p"
  unless strings.contains "s_string" && strings.contains "t_scalar" &&
      bits.contains "s_bv4" && bits.contains "t_scalar" do
    throw <| IO.userError "native scalar signature was not retained"

#print axioms string_scalar_replay
#print axioms bitvector_scalar_replay

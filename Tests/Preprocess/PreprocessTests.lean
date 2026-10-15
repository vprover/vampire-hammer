import VampireHammer
import VampireHammer.Preprocess

open VampireHammer
open VampireHammer.Preprocess
open Tptp.Data

/-! These are parser-AST checks, deliberately independent of formula decoding
and the inference backend. Current Vampire output supplies AC bridge nodes,
so `prepare` no longer runs the compatibility passes.  We invoke those passes
directly below to retain regression coverage for archived certificates. -/
#eval show IO Unit from do
  let transform := fun pass path => do
    let parsedResult ← parseVampireTSTP
      "" path
    let parsed ← IO.ofExcept parsedResult
    let .mk before := parsed
    let transformed ← IO.ofExcept <| pass parsed
    pure (before.length, transformed)

  let (activeBefore, active) ← transform prepare "Tests/testdata/preprocess-resolution.tstp"
  let .mk activeAfter := active
  unless activeAfter.length == activeBefore do
    throw <| IO.userError "the active preprocessing pipeline must not synthesize an AC bridge"

  let (before, transformed) ← transform resolutionClauses "Tests/testdata/preprocess-resolution.tstp"
  let .mk after := transformed
  unless after.length > before do
    throw <| IO.userError s!"expected inserted preprocessing nodes, got {before} -> {after.length} inputs"
  unless (reprStr transformed).contains "r_vh_resolution" do
    throw <| IO.userError "the reordered resolution must receive a separate core node"
  unless (reprStr transformed).contains "associativity_commutativity" do
    throw <| IO.userError "the reordered resolution must receive an AC bridge"
  if (reprStr transformed).contains "p_vh_ac" then
    throw <| IO.userError "a non-leading pivot must remain a position, not acquire a parent AC proxy"

  let (orderedBefore, ordered) ←
    transform resolutionClauses "Tests/testdata/preprocess-resolution-ordered.tstp"
  let .mk orderedAfter := ordered
  unless orderedAfter.length == orderedBefore do
    throw <| IO.userError "an already ordered resolution must not receive a no-op AC bridge"

  let (negativeFirstBefore, negativeFirst) ←
    transform resolutionClauses "Tests/testdata/preprocess-resolution-negative-first-ordered.tstp"
  let .mk negativeFirstAfter := negativeFirst
  unless negativeFirstAfter.length == negativeFirstBefore do
    throw <| IO.userError
      "a negative-first resolution in parent order must not receive an AC bridge"

  let (forwardBefore, forward) ←
    transform forwardSubsumptionClauses "Tests/testdata/preprocess-forward-subsumption.tstp"
  let .mk forwardAfter := forward
  unless forwardAfter.length > forwardBefore do
    throw <| IO.userError "a reordered forward subsumption step must receive an AC bridge"
  unless (reprStr forward).contains "r_vh_forward_subsumption_resolution" do
    throw <| IO.userError "the forward-subsumption core has the expected deterministic name"

  -- Vampire now emits its own `associativity_commutativity` step after an
  -- equality-resolution conclusion whose printed order differs from the
  -- natural parent tail.  Consequently this compatibility pass is not part
  -- of `prepare`.  Exercise it directly so the dormant fallback remains
  -- covered without changing the live pipeline's contract.
  let equalityParsedResult ← parseVampireTSTP
    ""
    "Tests/testdata/preprocess-equality-resolution.tstp"
  let equalityParsed ← IO.ofExcept equalityParsedResult
  let .mk equalityInputs := equalityParsed
  let equalityBefore := equalityInputs.length
  let equalityResolution ← IO.ofExcept <| equalityResolutionClauses equalityParsed
  let .mk equalityAfter := equalityResolution
  unless equalityAfter.length == equalityBefore + 1 do
    throw <| IO.userError
      s!"a reordered equality resolution must receive exactly one AC bridge, got {equalityBefore} -> {equalityAfter.length}"
  unless (reprStr equalityResolution).contains "f_child_vh_equality_resolution" do
    throw <| IO.userError
      "the equality-resolution core has the expected deterministic name"

  IO.println "TPTP clause-order preprocessing checks passed"

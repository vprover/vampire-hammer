import VampireHammer

open Auto.Embedding.Lam VampireHammer

/-! Checked wrapper signatures and separation from original input predicates. -/
#eval show IO Unit from do
  let domain := LamSort.atom 0
  let prop := LamSort.base .prop
  let relation := LamSort.func domain (.func domain prop)
  let problem : TFF.Problem := {
    text := "", sorts := #[("s_a0", domain)], facts := #[]
    symbols := #[("t_a0", .atom 0, .func domain domain),
      ("t_a1", .atom 1, .func domain prop), ("t_a2", .atom 2, domain)] }
  let original ← IO.FS.readFile "Tests/testdata/internal-definition-unfolding.tstp"
  let path := "/tmp/vampire-internal-definition-decoder-tests.tstp"
  let decode := fun (text : String) (problem : TFF.Problem) => do
    IO.FS.writeFile path text
    let proof ← IO.ofExcept (← parseVampireTSTP
      "" path)
    pure (Replay.decodeSteps problem proof)
  let decoded ← IO.ofExcept (← decode original problem)
  unless decoded.derivedSymbols.size == 2 &&
      decoded.derivedSymbols.all (·.kind == .internalDefinition) do
    throw <| IO.userError "expected both internal definition interpretations"
  let expectRejected := fun (text expected : String) => do
    match ← decode text problem with
    | .ok _ => throw <| IO.userError "accepted an invalid internal definition predicate"
    | .error message =>
      unless message.contains expected do
        throw <| IO.userError s!"unexpected diagnostic: {message}"
  expectRejected (original.replace "(s_a0 * s_a0) > $o" "(s_a0 * $o) > $o")
    "incompatible type"
  expectRejected (original.replace "sPN_t_a1: s_a0 > $o" "sPN_t_a1: (s_a0 * s_a0) > $o")
    "incompatible type"
  expectRejected (original.replace "sFN_t_a0" "sFN_unknown") "no known original symbol"
  -- An input relation named `sFN_t_a0` remains an abstract relation. Its
  -- spelling is not evidence of an equality interpretation.
  let inputPredicate := { problem with
    symbols := problem.symbols.push ("sFN_t_a0", .atom 3, relation) }
  let decoded ← IO.ofExcept (← decode original inputPredicate)
  unless !decoded.derivedSymbols.any (·.name == "sFN_t_a0") do
    throw <| IO.userError "reinterpreted an exported input predicate"
  IO.FS.removeFile path

import VampireHammer

open Auto.Embedding.Lam VampireHammer

/-! Check the omitted-declaration convention independently of Vampire's search.
Nullary formula names can be inferred as propositions; argument sorts must
still come from a declaration rather than from a guess in the decoder. -/
#eval show IO Unit from do
  let parse := fun path => do
    IO.ofExcept (← parseVampireTSTP
      "" path)
  let prop := LamSort.base .prop
  let problem ← IO.ofExcept <| TFF.exportProblem #[prop] #[] #[] #[.atom 0]
  let proof ← parse "Tests/testdata/predicate-definition-nullary.tstp"
  let decoded ← IO.ofExcept <| Replay.decodeSteps problem proof
  unless decoded.derivedSymbols.size == 1 && decoded.steps.size == 2 do
    throw <| IO.userError "expected one nullary predicate and both definition/folding nodes"
  let some symbol := decoded.derivedSymbols[0]?
    | throw <| IO.userError "missing decoded predicate definition"
  unless symbol.name == "sP0" && symbol.sort == prop &&
      symbol.kind == .predicateDefinition do
    throw <| IO.userError "the undeclared nullary predicate must be a proposition definition"

  let domain := LamSort.atom 0
  let typedProblem ← IO.ofExcept <| TFF.exportProblem #[.func domain prop] #[] #[domain]
    #[LamTerm.mkForallEF domain (.app domain (.atom 0) (.bvar 0))]
  let malformed ← parse "Tests/testdata/predicate-definition-missing-domain.tstp"
  match Replay.decodeSteps typedProblem malformed with
  | .ok _ => throw <| IO.userError "accepted an undeclared predicate with arguments"
  | .error message =>
    unless message.contains "too many arguments" do
      throw <| IO.userError s!"unexpected missing-domain diagnostic: {message}"

  -- Current Vampire uses the plural annotation even for a single deletion.
  -- Preserve the old spelling for archived proofs, and check both decoders.
  for spelling in ["removed_literal", "removed_literals"] do
    let inference : Backend.Inference := {
      rule := "factoring"
      parents := #[{ name := "parent" }]
      info := #[.application "unifier" #[.list #[
        .application "subs" #[.atom "parent", .list #[]]]],
        .application spelling #[.application "literal" #[.atom "parent", .number "1"]]]
    }
    let some factoring := inference.factoring?
      | throw <| IO.userError s!"factoring did not decode {spelling}"
    unless factoring.removedLiteral.parent == "parent" &&
        factoring.removedLiteral.index == 1 && factoring.substitutions.size == 1 do
      throw <| IO.userError s!"incorrect factoring certificate for {spelling}"
  IO.println "Formula-naming symbol decoding checks passed"

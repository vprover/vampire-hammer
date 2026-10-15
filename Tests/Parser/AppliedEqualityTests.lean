import VampireHammer

open Lean Meta Elab Command
open VampireHammer VampireHammer.Replay.Decode.Internal Auto.Embedding.Lam

private def formula (text : String) : IO THF.Term := do
  let .mk [.annotatedFormula (.thfAnnotated (.mk _ _ (.thfLogicFormula value) _))] ←
      IO.ofExcept (← parseVampireTSTPText "" text)
    | throw <| IO.userError "expected one THF formula"
  IO.ofExcept (THF.Syntax.term value)

#eval show IO Unit from do
  let domain := LamSort.atom 0
  let other := LamSort.atom 1
  let problem : TFF.Problem := {
    text := "", higherOrder := true, facts := #[],
    sorts := #[("s", domain), ("other", other)],
    symbols := #[("a", .atom 0, domain), ("b", .atom 1, other)] }
  let context : VampireHammer.Replay.Decode.Internal.Context := { problem }
  for head in ["(= @ a)", "( =\n@ a)", "((=) @ a)"] do
    let term ← formula s!"thf(f,plain,({head} @ a))."
    let decoded ← IO.ofExcept (decodeHigherOrderTerm term |>.run context)
    unless decoded.term == LamTerm.mkEq domain (.atom 0) (.atom 0) do
      throw <| IO.userError "applied equality changed its meaning"
    unless decoded.sort == .base .prop do
      throw <| IO.userError "applied equality has the wrong result sort"
  let term ← formula "thf(f,plain,((= @ a) @ b))."
  if (decodeHigherOrderTerm term |>.run context).isOk then
    throw <| IO.userError "accepted equality between different sorts"

  -- Quoted names, escaped quotes, source metadata and comments survive the
  -- retry. The only AST difference from the canonical spelling is grouping
  -- of the equality head, already shared by both sides below.
  let prologue := "% (= @ ignored)\n/* (= @ also_ignored) */\n"
  let suffix := ",file('source (= @ untouched)','fact \\' (= @ untouched)')).\n"
  let raw := prologue ++ "thf('name (= @ untouched)',plain,((= @ a) @ a)" ++ suffix
  let canonical := prologue ++ "thf('name (= @ untouched)',plain,(((=) @ a) @ a)" ++ suffix
  let parsed ← IO.ofExcept (← parseVampireTSTPText "" raw)
  let expected ← IO.ofExcept (← parseVampireTSTPText "" canonical)
  unless reprStr parsed == reprStr expected do
    throw <| IO.userError "equality compatibility changed names or annotations"
  let path : System.FilePath := "artifacts/applied-equality-parser.tstp"
  IO.FS.writeFile path raw
  let fromFile ← IO.ofExcept (← parseVampireTSTP "" path.toString)
  unless reprStr fromFile == reprStr expected do
    throw <| IO.userError "file and text parsers disagree on equality compatibility"
  IO.println "Applied equality: parser compatibility, annotations and typed decoding passed"

-- Embedded substitutions use a second interpreter. Its equality predicate
-- must have the same meaning and expose the left operand as a free variable.
run_cmd liftTermElabM do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let term := THF.Term.eqPartial (.variable "X")
    unless term.freeVariables == #["X"] do throwError "lost equality operand"
    let some predicate ← VampireHammer.Backend.Internal.materializeHigherOrderTerm
        term {} #[("X", x)] | throwError "could not materialize equality predicate"
    withLocalDeclD `y (mkConst ``Nat) fun y => do
      unless ← isDefEq (mkApp predicate y) (← mkEq x y) do
        throwError "materialized equality changed its meaning"
      checkWithKernel predicate

-- Vampire prints a negated equation as `~ a = b` (FOOL `$ite` definitions),
-- which TPTP writes `~ (a = b)`. Quoted text keeps its spelling.
#eval show IO Unit from do
  let printed := "tff(d,definition,((~ f(X0, b) = c => a = d) & (a != b => ~ a = b)), \
    file('~ x = y'))."
  let expected := "tff(d,definition,((~ (f(X0, b) = c) => a = d) & (a != b => ~ (a = b))), \
    file('~ x = y'))."
  let parsed ← IO.ofExcept (← parseVampireTSTPText "" printed)
  let reference ← IO.ofExcept (← parseVampireTSTPText "" expected)
  unless reprStr parsed == reprStr reference do
    throw <| IO.userError "negated equation changed its meaning"

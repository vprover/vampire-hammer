import VampireHammer
import VampireHammer.TptpPrinter

open Lean Meta Elab Command
open VampireHammer VampireHammer.Replay.Decode.Internal Auto.Embedding.Lam

#eval show IO Unit from do
  let sort := LamSort.atom 0
  let problem : TFF.Problem := {
    text := "", sorts := #[("s", sort)], facts := #[("fact0", .base .falseE)],
    symbols := #[("p", .atom 0, .base .prop), ("q", .atom 1, .base .prop),
      ("a", .atom 2, sort), ("b", .atom 3, sort), ("wrong", .atom 4, .base .nat)] }
  for dialect in ["tff", "fof", "thf"] do
    for expression in ["$ite(p,a,b)", "$ite((p & q),a,$ite(q,b,a))"] do
      let text := s!"{dialect}(f,plain,({expression} = a))."
      let parsed ← IO.ofExcept (← parseVampireTSTPText "" text)
      let steps ← IO.ofExcept (Replay.decodeSteps problem parsed)
      unless steps.steps.size == 1 do throw <| IO.userError "lost conditional formula"
      let rendered ← IO.ofExcept (TptpPrinter.render parsed)
      let roundTrip ← IO.ofExcept (← parseVampireTSTPText "" rendered)
      -- The writer adds parentheses (and THF has no AST of its own), so the
      -- round trip must preserve the decoded formula rather than the syntax.
      let again ← IO.ofExcept (Replay.decodeSteps problem roundTrip)
      unless again.steps.map (reprStr ·.formula) == steps.steps.map (reprStr ·.formula) do
        throw <| IO.userError "conditional round trip changed the formula"
      let path : System.FilePath := "artifacts/fool-parser.tstp"
      IO.FS.writeFile path text
      unless reprStr (← IO.ofExcept (← parseVampireTSTP "" path.toString)) == reprStr parsed do
        throw <| IO.userError "conditional file/text parser mismatch"
    for expression in ["$ite(a,a,b)", "$ite(p,a,wrong)", "$ite(p,a)"] do
      let parsed ← parseVampireTSTPText "" s!"{dialect}(f,plain,({expression} = a))."
      if let .ok parsed := parsed then
        if (Replay.decodeSteps problem parsed).isOk then
          throw <| IO.userError "accepted ill-sorted or malformed conditional"
  -- A conditional in comments/quoted source names must not change dialects.
  let text := "% $ite(p,a,b)\nfof(f,plain,p,file('quoted $ite(p,a,b)','fof'))."
  let .mk [.annotatedFormula (.fofAnnotated _)] ← IO.ofExcept (← parseVampireTSTPText "" text)
    | throw <| IO.userError "rewrote quoted/comment conditional text"

-- A malformed fresh-symbol definition must fail during local replay. These
-- definitions have no premises and cannot acquire facts from the caller.
run_cmd liftTermElabM do
  let sort := LamSort.atom 0
  let problem : TFF.Problem := {
    text := "", sorts := #[("s", sort)], facts := #[("fact0", .base .falseE)],
    symbols := #[("p", .atom 0, .base .prop), ("q", .atom 1, .base .prop),
      ("a", .atom 2, sort), ("b", .atom 3, sort)] }
  for (guards, expected) in [("(p => a = fresh) & (~p => b = fresh)", true),
      ("(p => a = fresh) & (q => b = fresh)", false),
      ("(p => a = fresh) & (p => b = fresh)", false)] do
    let text := "tff(t,type,fresh:s).\ntff(d,definition,(" ++ guards ++
      "),introduced(definition,[new_symbols(definition,[fresh])],[fool_ite_definition])).\n" ++
      "tff(f0,axiom,$false,file('fixture',fact0)).\n" ++
      "tff(f1,plain,$false,inference(definition_folding,[],[f0,d]))."
    let parsed ← IO.ofExcept (← parseVampireTSTPText "" text)
    let decoded ← IO.ofExcept (Replay.decodeSteps problem parsed)
    let saved ← saveState
    let accepted ← try
      let proof ← Replay.Internal.buildLocalProof problem decoded
      checkWithKernel proof.proof
      pure true
      catch _ => pure false
    saved.restore
    unless accepted == expected do throwError "conditional certificate check disagrees with expected validity"
  -- Embedded certificates preserve all three operands and check their types.
  withLocalDeclD `p (mkSort .zero) fun p =>
    withLocalDeclD `a (mkConst ``Nat) fun a =>
      withLocalDeclD `b (mkConst ``Nat) fun b => do
        let term := THF.Term.ite (.variable "P") (.variable "A") (.variable "B")
        unless term.freeVariables == #["P", "A", "B"] do throwError "lost conditional operand"
        let some value ← Backend.Internal.materializeHigherOrderTerm term {}
            #[("P", p), ("A", a), ("B", b)] | throwError "could not materialize conditional"
        unless ← isDefEq value (← mkAppM ``Auto.Bool.ite' #[p, a, b]) do
          throwError "conditional certificate changed its meaning"
        checkWithKernel value

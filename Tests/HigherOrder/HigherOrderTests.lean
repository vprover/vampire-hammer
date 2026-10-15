import VampireHammer.THF
import VampireHammer.Replay.Decode
import VampireHammer.TSTP
import VampireHammer.TptpPrinter
import VampireHammer.Backend.Instantiation
import VampireHammer.Backend.HigherOrder

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer
open VampireHammer.Backend
open VampireHammer.Backend.Internal

-- Real parser roundtrip: functions as arguments, nested lambda scope, and
-- proposition-valued binders, without collapsing Bool into Prop.
#eval show IO Unit from do
  let domain := LamSort.atom 0
  let fn := LamSort.func domain domain
  let pred := LamSort.func fn (.base .prop)
  let fact := LamTerm.app fn (.atom 0) (.lam domain (.bvar 0))
  let prop := LamSort.base .prop
  let facts := #[fact,
    LamTerm.mkForallEF prop (.mkEq prop (.bvar 0) (.bvar 0)),
    LamTerm.mkEq fn (.lam domain (.bvar 0)) (.lam domain (.bvar 0))]
  let .ok problem := THF.exportProblem #[pred] #[] #[domain] facts
    | throw (IO.userError "higher-order export failed")
  unless problem.higherOrder && problem.symbols[0]!.2.2 == pred do
    throw (IO.userError "lost higher-order signature")
  IO.FS.createDirAll "artifacts"
  IO.FS.writeFile "artifacts/higher-order-roundtrip.p" problem.text
  let .ok ast ← parseVampireTSTP ""
      "artifacts/higher-order-roundtrip.p"
    | throw (IO.userError "THF parser rejected exported problem")
  let .ok decoded := Replay.decodeSteps problem ast
    | throw (IO.userError "THF decoder rejected exported problem")
  unless decoded.steps.size == facts.size do
    throw (IO.userError "lost a higher-order formula during roundtrip")
  for (step, original) in decoded.steps.zip facts do
    unless step.formula.betaReduceHacky == original.betaReduceHacky do
      throw (IO.userError "higher-order formula changed during roundtrip")
  let .ok printed := TptpPrinter.render ast
    | throw (IO.userError "THF writer rejected exported problem")
  IO.FS.writeFile "artifacts/higher-order-printed.p" printed
  let .ok reparsed ← parseVampireTSTP ""
      "artifacts/higher-order-printed.p"
    | throw (IO.userError "THF writer emitted invalid syntax")
  let .ok redecoded := Replay.decodeSteps problem reparsed
    | throw (IO.userError "THF writer changed signature or term types")
  unless redecoded.steps.map (·.formula.betaReduceHacky) == decoded.steps.map (·.formula.betaReduceHacky) do
    throw (IO.userError "THF writer changed formula semantics")
  unless decoded.steps[0]?.any (·.formula == fact) do
    throw (IO.userError "lambda application changed during roundtrip")
  if (THF.exportProblem #[pred] #[] #[] #[fact]).isOk then
    throw (IO.userError "accepted missing domain inhabitation")
  let boolPredicate := LamSort.func (.base .bool) (.base .prop)
  let .ok boolProblem := THF.exportProblem #[boolPredicate] #[] #[]
      #[.app (.base .bool) (.atom 0) (.base (.bcst .trueb))]
    | throw (IO.userError "rejected a supported Boolean domain")
  unless boolProblem.sorts.contains ("s_bool", .base .bool) &&
      boolProblem.symbols[0]?.any (·.2.2 == boolPredicate) do
    throw (IO.userError "collapsed Bool into Prop")
  if (THF.exportProblem #[] #[] #[] #[.bvar 0]).isOk then
    throw (IO.userError "accepted an unbound exported variable")

-- Vampire's explicitly type-applied logical operators, including values
-- passed as arguments. Reprinting specializes them to ordinary typed binders.
#eval show IO Unit from do
  let text := "thf(i_type,type,i:$tType).\n" ++
    "thf(p_type,type,p:i>$o).\n" ++
    "thf(a_type,type,a:i).\n" ++
    "thf(q_type,type,q:((i>$o)>$o)>$o).\n" ++
    "thf(all,axiom,!! @ i @ p).\n" ++
    "thf(ex,axiom,?? @ i @ p).\n" ++
    "thf(op,axiom,q @ (!! @ i)).\n" ++
    "thf(eq,axiom,(@=) @ i @ a @ a).\n" ++
    "thf(scope,axiom,![VampireQuantified0:i>$o]:(!! @ i @ VampireQuantified0)).\n"
  let i := LamSort.atom 0
  let prop := LamSort.base .prop
  let pred := LamSort.func i prop
  let quant := LamSort.func pred prop
  let problem : TFF.Problem := {
    higherOrder := true
    text
    sorts := #[("i", i)]
    symbols := #[("p", .atom 0, pred), ("a", .atom 1, i), ("q", .atom 2, .func quant prop)]
    facts := #[] }
  IO.FS.writeFile "artifacts/higher-order-operators.p" text
  let .ok ast ← parseVampireTSTP ""
      "artifacts/higher-order-operators.p" | throw (IO.userError "logical operator parser failed")
  let decoded ← match Replay.decodeSteps problem ast with
    | .ok value => pure value
    | .error message => throw (IO.userError ("logical operator decoder failed: " ++ message))
  let expected := #[
    LamTerm.mkForallEF i (.app i (.atom 0) (.bvar 0)),
    LamTerm.mkExistEF i (.app i (.atom 0) (.bvar 0)),
    LamTerm.app quant (.atom 2) (.lam pred (.mkForallEF i (.app i (.bvar 1) (.bvar 0)))),
    LamTerm.mkEq i (.atom 1) (.atom 1),
    LamTerm.mkForallEF pred (.mkForallEF i (.app i (.bvar 1) (.bvar 0))) ]
  unless decoded.steps.map (·.formula.betaReduceHacky) == expected.map (·.betaReduceHacky) do
    throw (IO.userError "logical operator specialization changed typing or scope")
  let .ok printed := TptpPrinter.render ast | throw (IO.userError "logical operator writer failed")
  IO.FS.writeFile "artifacts/higher-order-operators-printed.p" printed
  let .ok reparsed ← parseVampireTSTP ""
      "artifacts/higher-order-operators-printed.p" | throw (IO.userError "logical operator reparse failed")
  let .ok redecode := Replay.decodeSteps problem reparsed | throw (IO.userError "logical operator re-decode failed")
  unless redecode.steps.map (·.formula.betaReduceHacky) == decoded.steps.map (·.formula.betaReduceHacky) do
    throw (IO.userError "logical operator writer changed semantics")

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

-- Lambda-bound X shadows free X. The other free variable Y stays free.
example (a : Nat) : a = a := by
  run_tac withMainContext do
    let a ← lookup "a"
    let term : THF.Term := .lam "X" (.named "s_nat")
      (.app (.lam "X" (.named "s_nat") (.variable "Y")) (.variable "X"))
    unless term.freeVariables == #["Y"] do throwError "incorrect lambda scope"
    let some value ← materializeHigherOrderTerm term {} #[("X", mkConst ``True), ("Y", a)]
      | throwError "typed lambda certificate rejected"
    unless ← isTypeCorrect value do throwError "ill-typed certificate"
    let expected ← withLocalDeclD `x (mkConst ``Nat) fun x => mkLambdaFVars #[x] a
    unless ← isDefEq value expected do throwError "lambda capture"
    let bad := THF.Term.app term (.truth true)
    if (← materializeHigherOrderTerm bad {} #[("Y", a)]).isSome then
      throwError "ill-typed higher-order application accepted"
  rfl

private def unitInput (proof target : Expr) : MetaM RuleInput := do
  pure {
    step := {
      name := "ho"
      formula := .base .trueE
      binders := #[]
      parents := #[{ name := "parent" }]
      sourceFact? := none
      inference? := none
      clauseLiterals? := none }
    target
    parents := #[{
      parent := { name := "parent" }
      binders := #[]
      existentialVariables := #[]
      componentBinders := #[]
      target := ← inferType proof
      clauseForm := false
      clauseLiterals? := none
      cnfCandidates := pure none
      proof }]
    clauseLiterals? := none
    sourceProof? := none
    sourceFVars := #[]
    symbols := {} }

example (f g : Nat → Nat) (h : f = g) : ∀ x, f x = g x := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let input ← unitInput (← lookup "h") (← goal.getType)
    let some proof ← higherOrderEquality input "argument_congruence"
      | throwError "argument congruence declined"
    unless ← isTypeCorrect proof do throwError "invalid congruence proof"
    goal.assign proof

-- The mapping changes binder order across different sorts. Incorrectly
-- swapping the Nat and Prop arguments must be declined before construction.
theorem negative_extensionality_mapped_sorts (f g : Nat → Nat → Nat)
    (h : ∀ n : Nat, ∀ P : Prop, P ∨ f n ≠ g n) :
    ∀ P : Prop, ∀ n : Nat,
      P ∨ f n (differenceWitness (f n) (g n)) ≠ g n (differenceWitness (f n) (g n)) := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let initial ← unitInput (← lookup "h") (← goal.getType)
    let sourceBinders : Array FormulaBinder := #[
      { name := "N", sort := .base .nat }, { name := "P", sort := .base .prop }]
    let childBinders : Array FormulaBinder := #[
      { name := "C", sort := .base .prop }, { name := "A", sort := .base .nat }]
    let input := { initial with
      step := { initial.step with binders := childBinders }
      parents := initial.parents.map fun parent => { parent with binders := sourceBinders } }
    let info : NegativeExtensionalityInfo := {
      literal := { parent := "parent", index := 1 }
      symbol := "difference"
      dependencies := #["N"]
      binderMapping? := some #[("N", "A"), ("P", "C")] }
    if (← negativeExtensionality input { info with
        binderMapping? := some #[("N", "C"), ("P", "A")] }).isSome then
      throwError "accepted a mapping across incompatible binder domains"
    let some proof ← negativeExtensionality input info
      | throwError "typed binder mapping declined"
    unless ← isTypeCorrect proof do throwError "invalid mapped extensionality proof"
    goal.assign proof

#print axioms negative_extensionality_mapped_sorts

example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let input ← unitInput (← lookup "h") (← goal.getType)
    let some proof ← higherOrderEquality input "positive_extensionality"
      | throwError "positive extensionality declined"
    unless ← isTypeCorrect proof do throwError "invalid extensionality proof"
    goal.assign proof

-- Negative extensionality changes only the selected literal; the clause
-- context is retained and cannot be dropped.
example (A : Prop) (f g : Nat → Nat) (h : A ∨ f ≠ g) :
    A ∨ f (differenceWitness f g) ≠ g (differenceWitness f g) := by
  run_tac withMainContext do
    let goal ← getMainGoal
    let input ← unitInput (← lookup "h") (← goal.getType)
    let info : NegativeExtensionalityInfo := {
      literal := { parent := "parent", index := 1 }
      symbol := "difference"
      dependencies := #[] }
    let some proof ← negativeExtensionality input info
      | throwError "negative extensionality with a clause context declined"
    unless ← isTypeCorrect proof do throwError "invalid clause-context proof"
    goal.assign proof

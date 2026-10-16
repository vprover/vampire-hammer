import Auto.Tactic
import VampireHammer.Options

/-! Provenance retained in checked proof terms, including cached proofs. -/

namespace VampireHammer.FactReporting

open Lean Meta Elab Tactic Meta.Tactic

/-- A transparent logical identity that retains the origin of an automatic
premise. Unlike mutable logging, it follows only the committed proof. -/
theorem additionalFact {P : Prop} (_origin : String) (proof : P) : P := proof

/-- Like `additionalFact`, for definitions that were unfolded automatically;
the text lists the definition names. -/
theorem unfoldedDefinitions {P : Prop} (_names : String) (proof : P) : P := proof

/-- Wrap `proof` of `type`, which the original proof's type unfolds to. -/
def markUnfolded (names : Array Name) (type proof : Expr) : Expr :=
  mkApp3 (mkConst ``unfoldedDefinitions) type
    (toExpr (" ".intercalate (names.toList.map toString))) proof

/-- Identity wrapper recording the portfolio strategy that found a proof. -/
theorem foundByStrategy (_strategy : String) (proof : False) : False := proof

def markStrategy (strategy? : Option String) (proof : Expr) : Expr :=
  match strategy? with
  | some strategy => mkApp2 (mkConst ``foundByStrategy) (toExpr strategy) proof
  | none => proof

/-- The recorded strategy of the first Vampire proof in `proof`, if any. -/
def foundStrategy? (proof : Expr) : Option String :=
  (proof.find? fun expression =>
    expression.getAppFn.isConstOf ``foundByStrategy && expression.getAppNumArgs >= 2).bind
    fun expression => match expression.getAppArgs[0]! with
      | .lit (.strVal text) => some text
      | _ => none

def markLemma (lemma : Auto.Lemma) : Auto.Lemma :=
  let proof := mkApp3 (mkConst ``additionalFact) lemma.type
    (toExpr (toString lemma.deriv)) lemma.proof
  { lemma with proof }

/-- Read markers from the completed proof, without expanding referenced
theorems. A theorem previously proved using automation remains an explicit
premise of this call. Shared subterms are visited once by `Meta.transform`.
Each result is a description and the term that supplies the fact. -/
def usedFacts (proof : Expr) : MetaM (Array (String × String)) := do
  let found ← IO.mkRef (#[] : Array (String × String))
  let _ ← Meta.transform proof (pre := fun expression => do
    if expression.getAppFn.isConstOf ``unfoldedDefinitions && expression.getAppNumArgs >= 3 then
      match expression.getAppArgs[1]! with
      | .lit (.strVal text) =>
        let entry := (s!"unfolded definitions: {text}", s!"(unfold := [{", ".intercalate (text.splitOn " ")}])")
        found.modify fun entries => if entries.contains entry then entries else entries.push entry
      | _ => pure ()
    if expression.getAppFn.isConstOf ``additionalFact && expression.getAppNumArgs >= 3 then
      let arguments := expression.getAppArgs
      let origin := match arguments[1]! with
        | .lit (.strVal text) => text
        | _ => "automatic premise"
      let statement := (← ppExpr arguments[0]!).pretty
      let entry := (s!"{origin}: {statement}", (← withOptions (·.setBool `pp.fullNames true) (ppExpr arguments[2]!)).pretty)
      found.modify fun entries => if entries.contains entry then entries else entries.push entry
    return .continue)
  return ← found.get

/-- The shortest suffix of `full` that resolves to exactly that constant in the
current namespace and open declarations. -/
def shortName (full : String) : CoreM String := do
  let name := full.toName
  let components := name.components
  for count in List.range components.length do
    let candidate := (components.drop (components.length - 1 - count)).foldl (fun n c => c.updatePrefix n) Name.anonymous
    let resolved := (← resolveGlobalName candidate).filter (·.2.isEmpty) |>.map (·.1)
    if resolved == [name] then return candidate.toString
  return full

/-- Shorten a suggestion term when it is a bare constant name. -/
def shortTerm (term : String) : CoreM String :=
  if term.isEmpty || term.any (fun c => c == ' ' || c == '(' || c == '*' || c == '[') || term == "*" then
    pure term
  else shortName term

/-- Emit once, after cache lookup or search has committed its winning proof.
Unused collected premises and failed speculative attempts produce no report.
The suggestion is a `vampire only` call that supplies the requested hints plus
exactly the automatic premises the proof used. -/
def report (goal : MVarId) (hints : TSyntax ``Auto.hints) : TacticM Unit := goal.withContext do
  unless vampire.reportFacts.get (← getOptions) do return
  let facts ← usedFacts (← instantiateMVars (mkMVar goal))
  unless facts.isEmpty do
    let requested := match hints.raw[0] with
      | .node _ _ args => if args.size == 3 then
          (args[1]!.getSepArgs.toList.map fun hint => (hint.reprint.getD "").trim)
        else ["*"] -- an omitted list means all local hypotheses in `vampire`
      | _ => []
    -- Direct proofs leave neither marker; a parallel race records the winner.
    let used := (← instantiateMVars (mkMVar goal)).getUsedConstants
    let mode :=
      if used.contains `VampireHammer.Replay.higherOrderRefutation then
        ["(parallel := false) (routedSlices := false) (higherOrder := true)"]
      else if used.contains `VampireHammer.Replay.firstOrderRefutation then
        ["(parallel := false) (routedSlices := false) (higherOrder := false)"]
      else []
    let strategy := match foundStrategy? (← instantiateMVars (mkMVar goal)) with
      | some text => [s!"(strategy := \"{text}\")"]
      | none => []
    let (settings, facts) := facts.partition (·.2.startsWith "(unfold")
    let settings ← settings.mapM fun (description, _) => do
      let names := (description.drop "unfolded definitions: ".length).toString.splitOn " "
      let names ← names.mapM (liftM ∘ shortName)
      pure (description, s!"(unfold := [{", ".intercalate names}])")
    let terms ← facts.foldlM (fun terms (_, term) => do
      let term ← shortTerm term
      pure (if terms.contains term then terms else terms ++ [term])) requested
    let call := s!"vampire only {"".intercalate ((settings.toList.map (·.2) ++ mode ++ strategy).map (· ++ " "))}[{", ".intercalate terms}]"
    TryThis.addSuggestion (← getRef) (s := call)

end VampireHammer.FactReporting

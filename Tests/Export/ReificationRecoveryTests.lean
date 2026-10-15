import VampireHammer.Export.Reification

open Lean Meta Elab Tactic VampireHammer.Export.Internal

private def proofDomainAlias (n : Nat) : Nat := n

-- Model a corrupt imported valuation: a Nat predicate resolves to a Bool
-- operation. The source proof remains a valid local proof, but its reified
-- application is ill-typed. It must never enter the checked assertion table.
elab "check_reification_recovery" : tactic => withMainContext do
  let predicateType ← mkArrow (mkConst ``Nat) (mkSort .zero)
  withLocalDeclD `predicate predicateType fun predicate => do
    let type := mkApp predicate (.lit (.natVal 0))
    withLocalDeclD `hypothesis type fun hypothesis => do
      let state : Auto.Reif.State := {
        declName? := none
        exprFVarVal := ({} : Std.HashMap FVarId Expr).insert predicate.fvarId! (mkConst ``Bool.not)
        tyCanMap := ({} : Std.HashMap Expr Expr).insert (mkConst ``Nat) (mkConst ``Nat) }
      let action : Auto.LamReif.ReifM Unit := do
        let optional : Auto.UMonoFact := ⟨hypothesis, type, .leaf "typeclass law corrupt valuation"⟩
        let usable : Auto.UMonoFact := ⟨mkConst ``True.intro, mkConst ``True, .leaf "required"⟩
        let terms ← reifyCheckedFacts #[optional, usable]
        unless terms.size == 1 && (← Auto.LamReif.getAssertions).size == 1 do
          throwError "invalid auxiliary fact survived, or valid fact was lost"
        let required := { optional with deriv := .leaf "vampire required negated goal" }
        let rejected ← try
          let _ ← reifyCheckedFacts #[required]
          pure false
        catch error =>
          pure ((← error.toMessageData.toString).contains "Auto.LamReif.reifTermCheckType")
        unless rejected do throwError "required invalid reification was silently dropped"
        unless (← Auto.LamReif.getAssertions).size == 1 do
          throwError "failed required reification poisoned the assertion table"
      let _ ← (action.run' {u := .zero}).run' state

  -- Two definitional presentations of the same proof domain used to become
  -- distinct atomic sorts. Retry must repair the alias and retain the source.
  let expanded := mkApp (mkConst ``proofDomainAlias) (.lit (.natVal 1))
  let literal := Expr.lit (.natVal 1)
  let domain ← mkEq expanded expanded
  let alias ← mkEq literal literal
  withLocalDeclD `predicate (← mkArrow domain (mkSort .zero)) fun predicate => do
    withLocalDeclD `argument alias fun argument => do
      let type := mkApp predicate argument
      withLocalDeclD `hypothesis type fun hypothesis => do
        let state : Auto.Reif.State := {
          declName? := none
          tyCanMap := ({} : Std.HashMap Expr Expr).insert domain domain |>.insert alias alias
            |>.insert (mkSort .zero) (mkSort .zero) }
        let action : Auto.LamReif.ReifM Unit := do
          let fact : Auto.UMonoFact := ⟨hypothesis, type, .leaf "required proof-domain alias"⟩
          let terms ← reifyCheckedFacts #[fact]
          unless terms.size == 1 && (← Auto.LamReif.getAssertions).size == 1 do
            throwError "definitional proof-sort repair lost the required fact"
        let _ ← (action.run' {u := .zero}).run' state

#eval show IO Unit from do
  let path : System.FilePath := "artifacts/reification-recovery.p.events.jsonl"
  if ← path.pathExists then IO.FS.removeFile path

set_option vampire.outputPath "artifacts/reification-recovery.p" in
example : True := by
  check_reification_recovery
  trivial

#eval show IO Unit from do
  let events ← IO.FS.readFile "artifacts/reification-recovery.p.events.jsonl"
  unless events.contains "source_expression" && events.contains "type_valuation" &&
      events.contains "atom_valuation" && events.contains "reification_repaired" do
    throw <| IO.userError "missing reification snapshot"

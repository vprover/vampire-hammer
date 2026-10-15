import VampireHammer.Export.Monomorphization
import VampireHammer.Export.Diagnostics
import VampireHammer.Export.SearchBudget

namespace VampireHammer.Export.Internal
open Lean Meta Auto.Embedding.Lam

/-- Repair only a representation mismatch at an application boundary. The
function's checked sort fixes its argument's type. A closed argument may use
that view only when the actual Lean value has a definitionally equal type.
Bound values and genuinely different dependent types remain unsupported. -/
private partial def reifyWithExpectedArguments (original : LocalContext)
    (locals : Std.HashMap FVarId Nat := {}) (bound : List LamSort := []) :
    Expr → Auto.LamReif.ReifM LamTerm
  | .app fn arg => do
    let function ← reifyWithExpectedArguments original locals bound fn
    let mut argument ← reifyWithExpectedArguments original locals bound arg
    let valuation ← Auto.LamReif.getLamTyValAtMeta
    let some (.func domain _) := function.lamCheck? valuation (bound[·]!)
      | throwError "reification repair: application head is not a checked function"
    unless argument.lamCheck? valuation (bound[·]!) == some domain do
      let value ← Auto.Reif.resolveVal arg
      unless !value.hasMVar && (collectFVars {} value).fvarIds.all original.contains do
        throwError "reification repair: argument is not closed over the source context"
      let (_, _, expected, _) ← Auto.LamReif.updownFunc domain
      unless ← withTransparency .default <| isDefEq (← inferType value) expected do
        throwError "reification repair: genuinely different argument type"
      argument ← Auto.LamReif.newTermExprAux value domain
    return .app domain function argument
  | .lam name type body info => do
    let domain ← Auto.LamReif.reifType type
    let body ← withLocalDecl name info type fun boundValue =>
      reifyWithExpectedArguments original (locals.insert boundValue.fvarId! locals.size)
        (domain :: bound) (body.instantiate1 boundValue)
    return .lam domain body
  | term => Auto.LamReif.processTermExpr locals term

private def repairSource (source : Auto.UMonoFact) : Auto.LamReif.ReifM LamTerm := do
  let term ← reifyWithExpectedArguments (← getLCtx) {} [] source.type
  let valuation ← Auto.LamReif.getLamTyValAtMeta
  unless term.lamCheck? valuation Auto.Embedding.Lam.dfLCtxTy == some (.base .prop) do
    throwError "reification repair did not produce a checked proposition"
  Auto.LamReif.newAssertion source.proof source.deriv term
  return term

/-- Reify each source transactionally. An invalid auxiliary fact cannot poison
the signature or prevent independent required facts from being exported.
Required facts still report the type error with their exact source/valuation. -/
def reifyCheckedFacts (sources : Array Auto.UMonoFact) : Auto.LamReif.ReifM (Array LamTerm) := do
  let mut terms := #[]
  let repairAllowance ← SearchAllowance.create 2000
  for source in sources do
    let savedLam ← get
    let savedReif ← liftM (show Auto.Reif.ReifM Auto.Reif.State from get)
    let savedMeta ← liftM (show MetaM Meta.SavedState from saveState)
    try
      terms := terms ++ (← Auto.LamReif.reifFacts #[source])
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      let message ← error.toMessageData.toString
      unless message.contains "Auto.LamReif.reifTermCheckType" do throw error
      let optional := isAutomaticSource source.deriv
      if ← Export.diagnosticsEnabled then
        let types ← Auto.LamReif.getTyVal
        let atoms ← Auto.LamReif.getVarVal
        liftM <| Export.diagnosticEvent "reification_type_error" [
          ("error", toJson message), ("optional", toJson optional),
          ("source", toJson (← ppExpr source.type).pretty),
          ("source_expression", toJson (reprStr source.type)),
          ("derivation", toJson (toString source.deriv)),
          ("type_valuation", toJson (types.map fun entry => reprStr entry.1)),
          ("type_valuation_pretty", toJson (← types.mapM fun entry => return (← ppExpr entry.1).pretty)),
          ("atom_valuation_pretty", toJson (← atoms.mapM fun entry => return (← ppExpr entry.1).pretty)),
          ("atom_valuation", toJson (atoms.map fun entry =>
            Json.mkObj [("value", toJson (reprStr entry.1)), ("sort", toJson (reprStr entry.2))]))]
      liftM savedMeta.restore
      set savedLam
      liftM (show Auto.Reif.ReifM Unit from set savedReif)
      let repaired? ← liftM <| repairAllowance.run ((repairSource source).run savedLam |>.run savedReif)
      if let some ((term, lamState), reifState) := repaired? then
        set lamState
        liftM (show Auto.Reif.ReifM Unit from set reifState)
        terms := terms.push term
        liftM <| Export.diagnosticEvent "reification_repaired" []
        continue
      liftM <| Export.diagnosticEvent "reification_repair_declined" [
        ("budget_exhausted", toJson ((← repairAllowance.remaining.get) == 0))]
      unless optional do throw error
      trace[vampire] "Omitting type-invalid auxiliary reification: {source.deriv}"
  return terms

end VampireHammer.Export.Internal

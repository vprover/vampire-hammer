import Auto.Tactic

open Lean Meta Elab Command Auto.Monomorphization

private structure LateScalar where
  value : Nat

private abbrev scalarCast : NatCast LateScalar := ⟨fun n => ⟨n⟩⟩
private abbrev ScalarAlias := LateScalar
private abbrev castAlias : NatCast ScalarAlias := scalarCast
private abbrev offsetCast : NatCast LateScalar := ⟨fun n => ⟨n + 1⟩⟩

private def castInstance (type cast : Expr) : MetaM ConstInst := do
  let expression := mkApp2 (mkConst ``NatCast.natCast [.zero]) type cast
  let some result ← ConstInst.ofExpr? #[] #[] expression
    | throwError "test cast is not a monomorphic constant instance"
  return result

-- Inferred signatures and binder reduction can expose a valid specialization
-- after saturation's instance collection. The abstraction cache starts empty.
run_cmd liftTermElabM do
  let ci ← castInstance (mkConst ``LateScalar) (mkConst ``scalarCast)
  let alias ← castInstance (mkConst ``ScalarAlias) (mkConst ``castAlias)
  let different ← castInstance (mkConst ``LateScalar) (mkConst ``offsetCast)
  let action : FVarRep.FVarRepM (Array FVarId × (FVarId × FVarId)) := do
    let first ← FVarRep.constInst2FVarId ci
    let repeated ← FVarRep.constInst2FVarId ci
    let equivalent ← FVarRep.constInst2FVarId alias
    unless first == repeated && first == equivalent do
      throwError "definitionally equal specializations did not share their representative"
    let other ← FVarRep.constInst2FVarId different
    unless first != other do
      throwError "different cast implementations were merged"
    unless (← FVarRep.getCiIdMap).size == 2 do
      throwError "late specialization introduced duplicate representatives"
    return (← FVarRep.getFfvars, (first, other))
  Auto.MetaState.runWithIntroducedFVars (action.run' { ciMap := {} }) fun (first, other) => do
    let value := mkApp (mkFVar first) (toExpr (7 : Nat))
    let otherValue := mkApp (mkFVar other) (toExpr (7 : Nat))
    unless ← isDefEq (← inferType value) (mkConst ``LateScalar) do
      throwError "late representative has an incorrect type"
    let field := mkApp (mkConst ``LateScalar.value) value
    let otherField := mkApp (mkConst ``LateScalar.value) otherValue
    unless (← isDefEq field (toExpr (7 : Nat))) &&
        (← isDefEq otherField (toExpr (8 : Nat))) do
      throwError "late specialization changed the original constant's value"
    check (← mkEqRefl value)

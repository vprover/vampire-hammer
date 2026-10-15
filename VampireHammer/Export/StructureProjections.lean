import Auto.Tactic

/-! Reflective structure projections for the checked object encoding. Only
constructors already present in the source are inspected. -/

namespace VampireHammer.Export.StructureProjections

open Lean Meta Auto.Embedding.Lam

structure Argument where
  sort : LamSort
  term : LamTerm
  value : Expr

structure Projection where
  sort : LamSort
  argument : LamTerm
  value : Expr

/-- Inspect a source symbol before interpreting each of its applications.
Reducible adapters and partially specialized constructor functions are allowed. -/
def isConstructor (function : Expr) : MetaM Bool :=
  lambdaTelescope function fun _ body => do
    let body ← withTransparency .reducible <| whnf body
    let .const name _ := body.getAppFn | return false
    let some (.ctorInfo info) := (← getEnv).find? name | return false
    return (getStructureInfo? (← getEnv) info.induct).isSome

/-- Match nondependent data fields of a constructor to its original arguments.
Values are closed over the same source binders before comparison. Projection
functions must be independent of those binders so they have a fixed TF0 type. -/
def collect (structureType constructor : Expr) (arguments : Array Argument) :
    MetaM (Array Projection) :=
  lambdaTelescope constructor fun parameters body => do
    let body ← withTransparency .reducible <| whnf body
    let .const name _ := body.getAppFn | return #[]
    let some (.ctorInfo info) := (← getEnv).find? name | return #[]
    let some _ := getStructureInfo? (← getEnv) info.induct | return #[]
    let mut result := #[]
    for field in getStructureFields (← getEnv) info.induct do
      let selected ← mkProjection body field
      if ← isProof selected then continue
      let selected ← mkLambdaFVars parameters selected
      for argument in arguments do
        unless ← withTransparency .all <| isDefEq selected argument.value do continue
        let projection? ← withLocalDeclD `structureObject structureType fun object => do
          let value ← mkProjection object field
          let type ← inferType value
          if type.hasAnyFVar (· == object.fvarId!) then return none
          let projection ← mkLambdaFVars #[object] value
          if projection.hasAnyFVar (fun id => parameters.any (·.fvarId! == id)) then return none
          return some projection
        if let some projection := projection? then
          result := result.push ⟨argument.sort, argument.term, projection⟩
        break
    return result

/-- Try to certify that the selected fields determine a structure value.
Constructor cases and equality substitution let Lean account for proof
irrelevance. Missing or dependent data fields simply prevent certification. -/
def proveExtensionality? (type : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    let goal ← mkFreshExprMVar type .syntheticOpaque
    let (variables, remaining) ← goal.mvarId!.introN 2
    let #[left, right] := variables | throwError "expected two structure values"
    withTransparency .all do
      for first in ← remaining.cases left do
        for second in ← first.mvarId.cases right do
          let (_, branch) ← second.mvarId.intros
          if let some branch ← branch.substEqs then branch.refl
    let proof ← instantiateMVars goal
    if ← (pure proof.hasMVar <||> (do return !(← isTypeCorrect proof))) then
      throwError "incomplete structure extensionality certificate"
    return some proof
  catch _ =>
    saved.restore
    return none

end VampireHammer.Export.StructureProjections

import Auto.Tactic

/-! Defining equivalences for proposition-valued class operations whose
instance reduces to a logical formula, such as
`instance : LE Val where le a b := a = b ∨ a = .Low ∨ b = .High`.
The operation stays an ordinary TF0 symbol; the added fact `∀ a b, a ≤ b ↔ …`
gives it its meaning and is proved by `Iff.rfl`. -/

register_option vampire.instanceDefinitions : Bool := {
  defValue := true
  descr := "Add the defining equivalence of proposition-valued class operations whose \
    instance is declared in the current module and reduces to a logical formula"
}

namespace VampireHammer.Export.InstanceDefinitions

open Lean Meta

def labelPrefix : String := "instance definition "

private def logicalHeads : Array Name :=
  #[``Eq, ``HEq, ``And, ``Or, ``Not, ``Iff, ``Exists, ``True, ``False]

/-- A body that is already first-order logic, rather than another opaque
symbol, `Bool` computation or recursor. -/
private def isLogicalFormula (body : Expr) : Bool :=
  body.isForall || match body.getAppFn with
    | .const name _ => logicalHeads.contains name
    | _ => false

/-- Library instances such as the order on `ℝ` can also reduce to formulas;
expanding them everywhere would add noise to established theories. Only
instances built from instance declarations of the current module qualify. -/
private def isLocalInstance (inst : Expr) : MetaM Bool := do
  let env ← getEnv
  inst.getUsedConstants.anyM fun name => do
    if (env.getModuleIdxFor? name).isSome then return false
    let some (.defnInfo info) := env.find? name | return false
    (do return (← isClass? info.type).isSome) <||>
      (do return (← forallTelescopeReducing info.type fun _ result => isClass? result).isSome)

/-- The class operation applied to its parameters and instance, when it is a
proposition-valued operation of a local instance with a logical definition. -/
private def candidate? (original : LocalContext) (expression : Expr) : MetaM (Option Expr) := do
  let .const name _ := expression.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  unless info.fromClass do return none
  let args := expression.getAppArgs
  unless args.size > info.numParams do return none
  let operation := mkAppN expression.getAppFn (args.extract 0 (info.numParams + 1))
  unless (collectFVars {} operation).fvarIds.all original.contains do return none
  unless ← isLocalInstance args[info.numParams]! do return none
  return some operation

/-- `∀ xs, operation xs ↔ body xs`, where the body is the instance-transparent
reduction of the operation. Returns none unless that body is a formula. -/
private def definitionLaw? (operation : Expr) : MetaM (Option Auto.Lemma) := do
  forallTelescopeReducing (← inferType operation) fun arguments result => do
    unless result.isProp do return none
    let application := mkAppN operation arguments
    let body ← withTransparency .instances <| whnf application
    if body == application || !isLogicalFormula body then return none
    let law ← mkForallFVars arguments (mkIff application body)
    let proof ← mkLambdaFVars arguments (mkApp (mkConst ``Iff.refl) application)
    unless ← isTypeCorrect proof do return none
    return some ⟨⟨proof, law, .leaf s!"{labelPrefix}{operation}"⟩, #[]⟩

/-- Inspect the requested source, and the generated definitions themselves so
that an operation defined through another one (`<` through `≤`) is covered.
At most eight definitions are added. -/
def collect (sources : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  unless vampire.instanceDefinitions.get (← getOptions) do return #[]
  let original ← getLCtx
  let mut pending := sources.map (·.type)
  let mut seen : Array Expr := #[]
  let mut laws := #[]
  while !pending.isEmpty && laws.size < 8 do
    let type ← instantiateMVars pending[0]!
    pending := pending.extract 1 pending.size
    let scan : StateRefT (Array Expr) MetaM Expr := Meta.transform type (post := fun expression => do
      if let some operation ← candidate? original expression then
        modify fun (found : Array Expr) =>
          if found.contains operation then found else found.push operation
      return .done expression)
    let (_, found) ← scan.run #[]
    for operation in found do
      if seen.contains operation || laws.size >= 8 then continue
      seen := seen.push operation
      let saved ← saveState
      try
        if let some law ← definitionLaw? operation then
          trace[vampire.premises] "Added the definition of {operation}: {law.type}"
          laws := laws.push law
          pending := pending.push law.type
      catch _ => saved.restore
  return laws

end VampireHammer.Export.InstanceDefinitions

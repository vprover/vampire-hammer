import Auto.Tactic

/-! Defining equations for structure projections of definitions whose body is
a structure literal, such as `PartialEquiv.symm e := { toFun := e.invFun, … }`.
Lean identifies `(e.symm).toFun y` with `e.invFun y` by unfolding; the
exported problem would otherwise see two unrelated symbols. The added fact
`∀ e y, (PartialEquiv.symm e).toFun y = e.invFun y` is proved by `rfl`.
Coercions such as `⇑e.symm` reach the same field through instance
projections; each step of that chain gets its own equation.

Facts are added rather than rewritten: monomorphization later instantiates
premises (for example with `e := e.symm`) and must still find both forms. -/

register_option vampire.projectionDefinitions : Bool := {
  defValue := true
  descr := "Add the defining equations of structure projections applied to \
    definitions whose body is a structure literal"
}

namespace VampireHammer.Export.ProjectionDefinitions

open Lean Meta

def labelPrefix : String := "projection definition "

/-- The projection function and the definition it is applied to, when the
expression is `S.f params (c args) rest` and unfolding `c args` can give a
structure literal. Class projections other than registered coercions
(`DFunLike.coe`, `SetLike.coe`, …) are only followed inside a chain: an
equation `a + b = Add.add a b` for every operator would only add noise. -/
private def candidate? (chained : Bool) (expression : Expr) :
    MetaM (Option (Name × Name)) := do
  let .const projection _ := expression.getAppFn | return none
  let some info ← getProjectionFnInfo? projection | return none
  if info.fromClass && !chained && (← getCoeFnInfo? projection).isNone then return none
  let some major := expression.getAppArgs[info.numParams]? | return none
  let .const definition _ := major.getAppFn | return none
  let some (.defnInfo _) := (← getEnv).find? definition | return none
  if (← getProjectionFnInfo? definition).isSome then return none
  -- Instances only provide the fields of class projections.
  if !info.fromClass && (← isInstance definition) then return none
  return some (projection, definition)

/-- The structure literal `c args` unfolds to, if any. -/
def structureLiteral? (major : Expr) : MetaM (Option (Expr × ConstructorVal)) := do
  let some body ← unfoldDefinition? major | return none
  let body ← whnfCore body
  -- Instances are often defined through other instances.
  let body ← if body.getAppFn.isConst then pure body else withReducibleAndInstances <| whnf body
  let .const constructor _ := body.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? constructor | return none
  return some (body, info)

/-- The field selected by the projection, applied to the remaining arguments. -/
private def reduceOnce? (expression : Expr) : MetaM (Option Expr) := do
  let .const projection _ := expression.getAppFn | return none
  let some info ← getProjectionFnInfo? projection | return none
  let args := expression.getAppArgs
  let some major := args[info.numParams]? | return none
  let some (body, constructor) ← structureLiteral? major | return none
  let some field := body.getAppArgs[constructor.numParams + info.i]? | return none
  return some (mkAppN field (args.extract (info.numParams + 1) args.size)).headBeta

/-- Reduce projections at the head through structure literals and through
definitions whose body is one, e.g. `⇑toNNRealHom x` to `ENNReal.toNNReal x`.
Nothing else is unfolded. -/
partial def unfoldProjections (expression : Expr) (fuel : Nat := 16) : MetaM Expr := do
  let expression := expression.headBeta
  if fuel == 0 then return expression
  let .const projection _ := expression.getAppFn | return expression
  let some info ← getProjectionFnInfo? projection | return expression
  let args := expression.getAppArgs
  let some major := args[info.numParams]? | return expression
  let major ← unfoldProjections major (fuel - 1)
  let reduced ← whnfCore major
  let literal? ← match reduced.getAppFn with
    | .const name _ => match (← getEnv).find? name with
      | some (.ctorInfo constructor) => pure (some (reduced, constructor))
      | _ => structureLiteral? major
    | _ => pure none
  let some (body, constructor) := literal? | return mkAppN expression.getAppFn (args.set! info.numParams major)
  let some field := body.getAppArgs[constructor.numParams + info.i]? | return expression
  unfoldProjections (mkAppN field (args.extract (info.numParams + 1) args.size)) (fuel - 1)

/-- `∀ args ys, S.f (c args) ys = field ys`, or `↔` for proposition-valued
fields, when unfolding `c args` gives a structure literal. -/
private def definitionLaw? (projection definition : Name) : MetaM (Option Auto.Lemma) := do
  let some info ← getProjectionFnInfo? projection | return none
  let .defnInfo constant ← getConstInfo definition | return none
  let levels := constant.levelParams.map Level.param
  forallTelescope constant.type fun arguments _ => do
    let major := mkAppN (.const definition levels) arguments
    let some (body, constructor) ← structureLiteral? major | return none
    let some field := body.getAppArgs[constructor.numParams + info.i]? | return none
    -- The structure is the first argument after the parameters; for a class
    -- projection it is instance-implicit, so it is passed positionally.
    let lhs ← instantiateMVars (← mkAppOptM projection
      ((Array.replicate info.numParams none).push (some major)))
    if lhs.hasMVar then return none
    forallTelescope (← inferType lhs) fun points result => do
      -- Proof fields carry no information; type-valued fields are not terms.
      if (← isProp (← inferType lhs)) || result.isSort then return none
      let application := mkAppN lhs points
      let value := (mkAppN field points).headBeta
      let (law, proof) ← if ← isProp result then
          pure (mkIff application value, mkApp (mkConst ``Iff.refl) application)
        else
          pure (← mkEq application value, ← mkEqRefl application)
      let binders := arguments ++ points
      let law ← mkForallFVars binders law
      let proof ← mkLambdaFVars binders (← mkExpectedTypeHint proof (← instantiateForall law binders))
      unless ← isTypeCorrect proof do return none
      return some ⟨⟨proof, law, .leaf s!"{labelPrefix}{projection} {definition}"⟩,
        constant.levelParams.toArray⟩

/-- Inspect the requested source, the generated equations, and each concrete
occurrence reduced by one step. The last follows a chain such as
`⇑e.symm y` → `EquivLike.coe (Equiv.symm e) y` → `(Equiv.symm e).toFun y` →
`e.invFun y`, one equation per step. At most sixteen equations are added. -/
def collect (sources : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  unless vampire.projectionDefinitions.get (← getOptions) do return #[]
  let mut pending : Array (Expr × Bool) := sources.map (·.type, false)
  let mut seen : Array (Name × Name) := #[]
  let mut visited : Array Expr := #[]
  let mut laws := #[]
  let mut steps := 0
  while !pending.isEmpty && laws.size < 16 && steps < 256 do
    steps := steps + 1
    let (expression, chained) := pending[0]!
    pending := pending.extract 1 pending.size
    let expression ← instantiateMVars expression
    let scan : StateRefT (Array (Expr × Name × Name)) MetaM Expr :=
      Meta.transform expression (post := fun subterm => do
        if let some pair ← candidate? chained subterm then
          modify fun (found : Array (Expr × Name × Name)) => found.push (subterm, pair)
        return .done subterm)
    let (_, found) ← scan.run #[]
    for (occurrence, projection, definition) in found do
      if laws.size >= 16 then break
      let saved ← saveState
      try
        unless seen.contains (projection, definition) do
          seen := seen.push (projection, definition)
          if let some law ← definitionLaw? projection definition then
            trace[vampire.premises] "Added the projection definition {law.type}"
            laws := laws.push law
            pending := pending.push (law.type, false)
        unless visited.contains occurrence do
          visited := visited.push occurrence
          if let some reduced ← reduceOnce? occurrence then
            pending := pending.push (reduced, true)
      catch _ => saved.restore
  return laws

end VampireHammer.Export.ProjectionDefinitions

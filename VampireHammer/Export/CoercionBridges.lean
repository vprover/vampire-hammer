import Auto.Tactic
import VampireHammer.Export.ProjectionDefinitions

/-! Facts relating coerced bundled maps to the plain functions of a problem,
such as `∀ x, ⇑ENNReal.toRealHom x = ENNReal.toReal x`. A generic law like
`map_prod (f : F) …` is only instantiated at coercions `⇑f` that occur in the
problem, and a goal stated with `ENNReal.toReal` contains none.

Bridges come from two sources:
* bundled maps given as hints: their coercion is compared, by definitional
  unfolding, with the functions applied in the problem, and the equation is
  proved by `rfl`;
* `@[simp]` lemmas of the shape `⇑B = f` or `⇑B x = f x`, for functions `f`
  of the problem, when a selected fact is a generic law about coerced maps. -/

register_option vampire.coercionBridges : Bool := {
  defValue := true
  descr := "Relate coerced bundled maps to the plain functions of the problem \
    (from bundled-map hints and `@[simp]` coercion lemmas)"
}

namespace VampireHammer.Export.CoercionBridges

open Lean Meta

def labelPrefix : String := "coercion bridge "

/-- Mathlib's coercion of bundled maps; this package does not import Mathlib. -/
private def dfunLikeCoe : Name := `DFunLike.coe

/-- `∀ xs ys, lhs ys = rhs ys` from a proof of `∀ xs, lhs = rhs` at a
function type. Other statements are returned unchanged. -/
private def pointwise (proof type : Expr) : MetaM (Expr × Expr) :=
  forallTelescope type fun xs body => do
    let some (domain, lhs, rhs) := body.eq? | return (proof, type)
    forallTelescope domain fun ys _ => do
      if ys.isEmpty then return (proof, type)
      let mut equation := mkAppN proof xs
      for y in ys do equation ← mkCongrFun equation y
      let law ← mkEq (mkAppN lhs ys).headBeta (mkAppN rhs ys).headBeta
      let binders := xs ++ ys
      return (← mkLambdaFVars binders (← mkExpectedTypeHint equation law),
        ← mkForallFVars binders law)

/-- Functions `g` applied as `g x` in the facts, without bound variables. -/
private def appliedFunctions (types : Array Expr) : MetaM (Array Expr) := do
  let original ← getLCtx
  let mut found : Array Expr := #[]
  for type in types do
    let scan : StateRefT (Array Expr) MetaM Expr :=
      Meta.transform (← instantiateMVars type) (post := fun expression => do
        if let .app function _ := expression then
          if !function.hasLooseBVars && (collectFVars {} function).fvarIds.all original.contains then
            modify fun (found : Array Expr) =>
              if found.contains function || found.size >= 64 then found else found.push function
        return .done expression)
    found := (← scan.run found).2
  return found

/-- `⇑value`, when `value` is a bundled map. -/
private def coercion? (value : Expr) : MetaM (Option Expr) := do
  try
    let coercion ← instantiateMVars
      (← mkAppOptM dfunLikeCoe #[none, none, none, none, some value])
    return if coercion.hasMVar then none else some coercion
  catch _ => return none

/-- Whether the definitions of `left` and `right` agree, within a small budget. -/
private def definitionallyEqual (left right : Expr) : MetaM Bool := do
  let saved ← saveState
  let result ← tryCatchRuntimeEx
    (withNewMCtxDepth <| Auto.Meta.withMaxHeartbeats 2000 do
      (isDefEq (← inferType left) (← inferType right)) <&&> isDefEq left right)
    (fun _ => pure false)
  saved.restore
  return result

/-- Bridges for closed bundled maps given as hints, `(value, label, params)`.
The coercion is equated with a function applied in `facts` when both unfold
to the same term; otherwise with its projection-reduced form, if that differs. -/
def hintBridges (values : Array (Expr × String × Array Name)) (facts : Array Auto.Lemma) :
    MetaM (Array Auto.Lemma) := do
  unless vampire.coercionBridges.get (← getOptions) do return #[]
  if values.isEmpty then return #[]
  let functions ← appliedFunctions (facts.map (·.type))
  let mut laws := #[]
  for (value, label, params) in values do
    let some coercion ← coercion? value | continue
    let mut targets := #[]
    for function in functions do
      if function != coercion && targets.size < 2 && (← definitionallyEqual coercion function) then
        targets := targets.push function
    if targets.isEmpty then
      let reduced ← forallTelescope (← inferType coercion) fun points _ => do
        let application := mkAppN coercion points
        let reduced ← ProjectionDefinitions.unfoldProjections application
        if reduced == application then return none
        return some (← mkLambdaFVars points reduced)
      if let some reduced := reduced then targets := #[reduced]
    for target in targets do
      let saved ← saveState
      try
        let equation ← mkEq coercion target
        let proof ← mkExpectedTypeHint (← mkEqRefl coercion) equation
        let (proof, law) ← pointwise proof equation
        unless ← isTypeCorrect proof do saved.restore; continue
        trace[vampire.premises] "Added the coercion bridge {law}"
        laws := laws.push ⟨⟨proof, law, .leaf s!"{label} coercion"⟩, params⟩
      catch _ => saved.restore
  return laws

/-- The function `f` of a canonical bridge `∀ xs, ⇑(B xs) = f xs`, such as
`NNReal.coe_toRealHom : ⇑toRealHom = toReal`: an unapplied coercion equated
with a function, both applied to parameters only. Lemmas about applied values
(`…_apply`) are not bridges. Read syntactically. -/
private def bridgeTarget? (type : Expr) : Option Name := do
  let some (_, lhs, rhs) := type.getForallBody.eq? | none
  guard (lhs.isAppOfArity dfunLikeCoe 5)
  let coerced ← lhs.getAppArgs[4]?
  let .const bundled _ := coerced.getAppFn | none
  let .const function _ := rhs.getAppFn | none
  guard (bundled != function)
  -- Parameters are the lemma's bound variables, `#i` after `getForallBody`.
  guard ((coerced.getAppArgs ++ rhs.getAppArgs).all (·.isBVar))
  pure function

/-- Whether a statement is a generic law about coerced maps, `⇑f` for a bound `f`. -/
private def hasGenericCoercion (type : Expr) : Bool :=
  (type.find? fun expression =>
    expression.isAppOf dfunLikeCoe &&
      (expression.getAppArgs[4]?.any (·.hasLooseBVars))).isSome

/-- Head constants of the applications in an expression, read syntactically. -/
private partial def appliedConstants (expression : Expr) (found : NameSet := {}) : NameSet :=
  match expression with
  | .app .. =>
    let found := match expression.getAppFn with
      | .const name _ => found.insert name
      | function => appliedConstants function found
    expression.getAppArgs.foldl (fun found argument => appliedConstants argument found) found
  | .lam _ type body _ | .forallE _ type body _ => appliedConstants body (appliedConstants type found)
  | .letE _ type value body _ =>
    appliedConstants body (appliedConstants value (appliedConstants type found))
  | .mdata _ inner | .proj _ _ inner => appliedConstants inner found
  | _ => found

/-- lean-auto labels local hypotheses, including the negated goal, `lctxLem`. -/
private partial def fromLocalContext : Auto.DTr → Bool
  | .leaf label => label.startsWith "lctxLem"
  | .node _ premises => premises.any fromLocalContext

/-- `@[simp]` bridges `⇑B = f` for the functions `f` of `facts`, when some
fact is a generic law about coerced maps. At most four are added. -/
def collect (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  unless vampire.coercionBridges.get (← getOptions) do return #[]
  unless facts.any (hasGenericCoercion ·.type) do return #[]
  -- Target functions are applied in the goal or a local hypothesis; class
  -- operations such as `HMul.hMul`, and constants occurring only in types or
  -- instances, would select unrelated lemmas.
  let mut constants : NameSet := {}
  for fact in facts do
    unless fromLocalContext fact.deriv do continue
    for name in appliedConstants (← instantiateMVars fact.type) do
      unless (← getProjectionFnInfo? name).any (·.fromClass) do
        constants := constants.insert name
  let env ← getEnv
  let simpTheorems ← getSimpTheorems
  let candidates := simpTheorems.lemmaNames.fold (init := #[]) fun candidates origin =>
    match origin with
    | .decl name _ false =>
      match env.find? name with
      | some info =>
        match bridgeTarget? info.type with
        | some function => if constants.contains function then candidates.push name else candidates
        | none => candidates
      | none => candidates
    | _ => candidates
  let mut laws := #[]
  for name in candidates.qsort (·.toString < ·.toString) do
    if laws.size >= 4 then break
    let saved ← saveState
    try
      let ⟨⟨proof, type, _⟩, params⟩ ← Auto.Lemma.ofConst name (.leaf "")
      let (proof, law) ← pointwise proof type
      trace[vampire.premises] "Added the coercion bridge {name}: {law}"
      laws := laws.push ⟨⟨proof, law, .leaf s!"{labelPrefix}{name}"⟩, params⟩
    catch _ => saved.restore
  return laws

end VampireHammer.Export.CoercionBridges

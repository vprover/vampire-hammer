import VampireHammer.Export.Diagnostics
import VampireHammer.Export.Monomorphization

/-!
Cheap structural routing between the first-order (TF0) and native higher-order
(TH0) exports. Features are read from the Lean statements of the user-visible
facts before any monomorphization; nothing here is expensive or searches.

Ordinary function-typed constants alone never count: they occur in most
first-order statements. Evidence is a *bound* function or predicate variable
together with function values passed as arguments, surviving lambdas or
extensional equalities of functions.
-/

namespace VampireHammer.Export.Internal.Routing

open Lean Meta

/-- The two prepared representations. -/
inductive Route where
  | firstOrder
  | higherOrder
deriving BEq, Inhabited, Repr

def Route.other : Route → Route
  | .firstOrder => .higherOrder
  | .higherOrder => .firstOrder

def Route.name : Route → String
  | .firstOrder => "fo"
  | .higherOrder => "ho"

structure Features where
  /-- Quantifier binders whose domain is a function or predicate type. -/
  boundFunctions : Nat := 0
  /-- Arguments that are lambdas or bound function variables. -/
  functionArguments : Nat := 0
  /-- Lambdas that are not the body of a binder-like head such as `Exists`. -/
  lambdas : Nat := 0
  /-- Equalities at a function or predicate type. -/
  extensionalEqualities : Nat := 0
  /-- Closed function domains of the bound function variables. -/
  domains : Array Expr := #[]

def Features.evidence (features : Features) : Nat :=
  features.functionArguments + features.lambdas + features.extensionalEqualities

/-- Strong structural evidence for native higher-order search. -/
def Features.strong (features : Features) : Bool :=
  (features.boundFunctions > 0 && features.evidence > 0) ||
  (features.extensionalEqualities > 0 && features.lambdas > 0)

def Features.add (a b : Features) : Features where
  boundFunctions := a.boundFunctions + b.boundFunctions
  functionArguments := a.functionArguments + b.functionArguments
  lambdas := a.lambdas + b.lambdas
  extensionalEqualities := a.extensionalEqualities + b.extensionalEqualities
  domains := a.domains ++ b.domains

/-- A function or predicate type, not a type family or a proposition that
happens to be a `∀` statement. -/
private def isFunctionType (type : Expr) : MetaM Bool := do
  let rec codomainIsSort : Expr → Bool
    | .sort _ => true
    | .forallE _ _ body _ => codomainIsSort body
    | _ => false
  unless type.isForall do return false
  if codomainIsSort type then return false
  return !(← isProp type)

/-- Binder-like heads whose lambda argument is a quantified body. -/
private def isBinderHead (name : Name) : Bool :=
  name == ``Exists || name == `ExistsUnique || name == ``Sigma || name == ``PSigma ||
  name == ``Subtype || name == ``Classical.epsilon

/-- Walk `e`, replacing binders by local variables. `bound` lists the
variables introduced by the walk, so domains depending on them are not
reported as closed. -/
private partial def collect (e : Expr) (bound : List FVarId) : MetaM Features := do
  let mut out : Features := {}
  let closed (domain : Expr) : Bool :=
    !domain.hasLooseBVars && !domain.hasAnyFVar (bound.contains ·)
  let isFunctionValue (arg : Expr) : MetaM Bool := do
    match arg with
    | .lam .. => return true
    | .fvar id =>
      if !bound.contains id then return false
      isFunctionType (← inferType arg)
    | _ => return false
  let under (name : Name) (info : BinderInfo) (domain body : Expr) : MetaM Features :=
    withLocalDecl name info domain fun x =>
      collect (body.instantiate1 x) (x.fvarId! :: bound)
  match e with
  | .forallE name domain body info =>
    if info.isExplicit && (← isFunctionType domain) then
      out := { out with boundFunctions := 1 }
      if closed domain then out := { out with domains := #[domain] }
    out := out.add (← collect domain bound)
    out := out.add (← under name info domain body)
  | .lam name domain body info =>
    out := { out with lambdas := 1 }
    out := out.add (← collect domain bound)
    out := out.add (← under name info domain body)
  | .letE _ type value body _ =>
    out := out.add (← collect type bound) |>.add (← collect value bound)
    out := out.add (← collect (body.instantiate1 value) bound)
  | .mdata _ inner | .proj _ _ inner => out ← collect inner bound
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let binderHead := match fn with
      | .const name _ => isBinderHead name
      | _ => false
    if fn.isConstOf ``Eq then
      if let some type := args[0]? then
        if ← isFunctionType type then
          out := { out with extensionalEqualities := 1 }
    for arg in args do
      match arg with
      | .lam name domain body info =>
        if binderHead then
          -- The binder itself is quantification, not a surviving lambda.
          if ← isFunctionType domain then
            out := { out with boundFunctions := out.boundFunctions + 1 }
            if closed domain then out := { out with domains := out.domains.push domain }
          out := out.add (← collect domain bound)
          out := out.add (← under name info domain body)
        else
          out := { out with functionArguments := out.functionArguments + 1 }
          out := out.add (← collect arg bound)
      | _ =>
        if ← isFunctionValue arg then
          out := { out with functionArguments := out.functionArguments + 1 }
        out := out.add (← collect arg bound)
    unless fn.isConst || fn.isFVar do out := out.add (← collect fn bound)
  | _ => pure ()
  return out

/-- Features of the facts the user or goal contributed. Automatically collected
laws and generated facts are skipped: they do not describe the problem. An
expression that cannot be inspected contributes nothing. -/
def features (lemmas : Array Auto.UMonoFact) : MetaM Features := do
  let mut acc : Features := {}
  for lemma in lemmas do
    if isAutomaticSource lemma.deriv then continue
    try
      acc := acc.add (← collect (← instantiateMVars lemma.type) [])
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
  return acc

/-- Whether the final codomain of an arrow chain is cheaply known inhabited. -/
private def cheaplyInhabited (type : Expr) : MetaM Bool := do
  let mut codomain := type
  while codomain.isArrow do codomain := codomain.bindingBody!
  if codomain.hasLooseBVars then return false
  if codomain.isProp || codomain == mkSort Level.zero then return true
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if decl.type == type || decl.type == codomain then return true
  withOptions (fun options => options.set `synthInstance.maxHeartbeats 500) do
    try
      let level ← getLevel codomain
      if (← synthInstance? (mkApp (mkConst ``Nonempty [level]) codomain)).isSome then return true
      return (← synthInstance? (mkApp (mkConst ``Inhabited [level]) codomain)).isSome
    catch _ => return false

/-- Whether every closed bound-function domain has a cheap inhabitant: a
supplied function, or an inhabited codomain giving a constant function. A
failure means "prefer first-order", not that the domain is empty. -/
def higherOrderViable (features : Features) : MetaM Bool := do
  for domain in features.domains do
    unless ← cheaplyInhabited domain do return false
  return true

/-- Choose the first route: first-order unless the evidence is strong and a
native export is cheaply viable. -/
def choose (lemmas : Array Auto.UMonoFact) : MetaM (Route × Features × Bool) := do
  let features ← features lemmas
  if !features.strong then return (.firstOrder, features, true)
  let viable ← higherOrderViable features
  return (if viable then .higherOrder else .firstOrder, features, viable)

def Features.toJson (features : Features) : Json :=
  Json.mkObj [("bound_functions", Lean.toJson features.boundFunctions),
    ("function_arguments", Lean.toJson features.functionArguments),
    ("lambdas", Lean.toJson features.lambdas),
    ("extensional_equalities", Lean.toJson features.extensionalEqualities)]

end VampireHammer.Export.Internal.Routing

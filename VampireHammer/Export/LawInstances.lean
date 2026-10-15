import Auto.Tactic
import VampireHammer.Options

/-!
Checked algebraic laws discovered from `Std` law instances for the binary
operations occurring in the source problem.

Every fact below is a Lean proof obtained by projecting a synthesized
`Std.Commutative`, `Std.Associative`, `Std.IdempotentOp` or `Std.LawfulIdentity`
instance; no mathematical theory is registered in this file.  Operation keys are
built from the applications that actually occur in the requested facts, so
instance search is anchored on the problem itself, and every type whose
algebraic structure is registered through the typeclass system (Lean core,
mathlib, or a local instance) contributes its laws.

`Std.LawfulIdentity`'s unit is an output parameter, but Lean's instance
resolution does not infer it from an unknown metavariable.  Units are therefore
taken from the closed constant applications of the source problem: a law about a
unit that never occurs in the source could not connect to it anyway.
-/

namespace VampireHammer.Export.LawInstances

open Lean Meta

def labelPrefix : String := "law instance "

/-- Maximum number of distinct binary operations to inspect. -/
private def maxOperations : Nat := 16

/-- Maximum number of distinct closed constant applications to try as units. -/
private def maxUnits : Nat := 8

/-- Maximum number of generated law facts. -/
private def maxFacts : Nat := 24

/-- Maximum number of expression nodes visited per source fact. -/
private def maxVisits : Nat := 8192

private structure ScanState where
  operations : Array Expr := #[]
  units : Array Expr := #[]
  visits : Nat := 0

/-- A short readable description of an operation for fact labels. -/
private def describeOp : Expr → String
  | .lam _ _ body _ => describeOp body
  | application =>
    match application.getAppFn with
    | .const name _ => name.toString
    | _ => "operation"

/-- A short readable description of a unit candidate for trace diagnostics. -/
private def describeTerm (expression : Expr) : String := s!"{expression}"

/-- Synthesize an instance, treating a failed or stuck search as `none` and
restoring the metavariable state a failed attempt may have polluted. -/
private def trySynthInstance? (goal : Expr) : MetaM (Option Expr) := do
  let saved ← saveState
  try
    synthInstance? goal
  catch _ =>
    saved.restore
    return none

/-- The carrier of a binary operation `op : α → α → α`, with its universe. -/
private def carrierOf (op : Expr) : MetaM (Expr × Level) := do
  let opType ← instantiateMVars (← inferType op)
  let .forallE _ carrier _ _ := opType | throwError "operation is not a binary function"
  let .sort level ← instantiateMVars (← whnfD (← inferType carrier))
    | throwError "operation carrier is not a sort"
  return (carrier, level)

/-- Build the binary operation an application applies to its last two
arguments: `a + b` yields `fun x y => x + y`.  The result is kept only when it
is a closed function between one non-`Prop` carrier, matching the signature of
the `Std` law classes.  The application's arguments are fvar-based: the
traversal below opens binders before descending, so type inference never sees
bound variables. -/
private def operationOf (application : Expr) : MetaM (Option Expr) := do
  let fnHead := application.getAppFn
  let arguments := application.getAppArgs
  unless arguments.size >= 2 do return none
  let left := arguments[arguments.size - 2]!
  let right := arguments.back!
  let leftType ← instantiateMVars (← inferType left)
  let rightType ← instantiateMVars (← inferType right)
  let resultType ← instantiateMVars (← inferType application)
  unless ← isDefEq leftType rightType do return none
  unless ← isDefEq rightType resultType do return none
  -- Propositional connectives already have complete first-order treatment,
  -- and type-valued arguments belong to type formers, not algebraic laws.
  if ← isDefEq leftType (mkSort Level.zero) then return none
  if leftType.isSort then return none
  let saved ← saveState
  try
    let op ← withLocalDeclD `x leftType fun x =>
      withLocalDeclD `y leftType fun y => do
        let body := mkAppN fnHead (arguments.take (arguments.size - 2) ++ #[x, y])
        mkLambdaFVars #[x, y] body
    -- Dependent applications can survive the argument checks above but still
    -- produce an ill-typed abstraction; `inferType` rejects those here.
    let _ ← inferType op
    if op.hasLooseBVars then return none
    return some op
  catch _ =>
    saved.restore
    return none

/-- The operation an application applies to its last two arguments, provided
all of its parameters belong to the caller's context. -/
private def operationAnchor (original : LocalContext) (application : Expr) :
    MetaM (Option Expr) := do
  let saved ← saveState
  try
    let some op ← operationOf application | return none
    unless (collectFVars {} op).fvarIds.all original.contains do return none
    return some op
  catch _ =>
    saved.restore
    return none

/-- A closed small constant application usable as an identity unit.

The candidate must be data rather than a proposition, and its type must not be
a class: quantifier bodies, equalities and class-instance paths are not units,
while numerals such as `@OfNat.ofNat Int 0 instOfNatInt` and empty collections
are. -/
private def unitAnchor (original : LocalContext) (expression : Expr) :
    MetaM (Option Expr) := do
  unless expression.isApp
      && expression.getAppFn.isConst
      && expression.getAppNumArgs <= 4 do return none
  unless (collectFVars {} expression).fvarIds.all original.contains do return none
  let unitType ← instantiateMVars (← inferType expression)
  if ← isProp expression then return none
  if (← Meta.isClass? unitType).isSome then return none
  return some expression

/-- Visit one expression node: record operation and unit anchors here, then
recurse.  Binders are opened with fresh free variables so that `inferType` and
instance search see ordinary local terms; anchors that would mention one of
those temporary binders are rejected against the caller's original context. -/
private partial def scan (original : LocalContext) (state : IO.Ref ScanState)
    (expression : Expr) : MetaM Unit := do
  let current ← state.get
  if current.visits >= maxVisits
      || (current.operations.size >= maxOperations && current.units.size >= maxUnits) then
    return
  state.set { current with visits := current.visits + 1 }
  match expression with
  | .app .. =>
    unless current.operations.size >= maxOperations do
      if let some op ← operationAnchor original expression then
        let found ← state.get
        unless found.operations.contains op do
          state.set { found with operations := found.operations.push op }
    unless (← state.get).units.size >= maxUnits do
      if let some unit ← unitAnchor original expression then
        let found ← state.get
        unless found.units.contains unit do
          state.set { found with units := found.units.push unit }
    let fnHead := expression.getAppFn
    let arguments := expression.getAppArgs
    scan original state fnHead
    for argument in arguments do
      scan original state argument
  | .forallE _ domain body _ =>
    scan original state domain
    withLocalDecl `vampireScan .default domain fun boundVar =>
      scan original state (body.instantiate1 boundVar)
  | .lam _ domain body _ =>
    scan original state domain
    withLocalDecl `vampireScan .default domain fun boundVar =>
      scan original state (body.instantiate1 boundVar)
  | .letE _ letType value body _ =>
    scan original state letType
    scan original state value
    withLocalDecl `vampireScan .default letType fun boundVar =>
      scan original state (body.instantiate1 boundVar)
  | .mdata _ inner => scan original state inner
  | .proj _ _ inner => scan original state inner
  | _ => pure ()

/-- One law fact.  The projected proof keeps its type up to beta reduction, so
the statement is beta-normalized here to keep reification first-order. -/
private def lawOf (label : String) (proof : Expr) : MetaM Auto.Lemma := do
  let type ← instantiateMVars (← inferType proof)
  let type ← Lean.Core.betaReduce type
  if proof.hasMVar || type.hasMVar then throwError "law certificate contains metavariables"
  return ⟨⟨proof, type, .leaf label⟩, #[]⟩

/-- `Std.Commutative`, `Std.Associative` and `Std.IdempotentOp` laws of one
operation.  Class arguments are read back from the synthesized instance so the
projected proof is exactly typed. -/
private def operationLawsOf (op : Expr) : MetaM (Array Auto.Lemma) := do
  let description := describeOp op
  let (carrier, level) ← carrierOf op
  let mut facts := #[]
  if let some inst ← trySynthInstance? (mkApp2 (.const ``Std.Commutative [level]) carrier op) then
    let instType ← instantiateMVars (← inferType inst)
    let #[carrier', op'] := instType.getAppArgs | throwError "unexpected Commutative instance type"
    let proof := mkApp3 (.const ``Std.Commutative.comm [level]) carrier' op' inst
    facts := facts.push (← lawOf s!"{labelPrefix}commutativity of {description}" proof)
  if let some inst ← trySynthInstance? (mkApp2 (.const ``Std.Associative [level]) carrier op) then
    let instType ← instantiateMVars (← inferType inst)
    let #[carrier', op'] := instType.getAppArgs | throwError "unexpected Associative instance type"
    let proof := mkApp3 (.const ``Std.Associative.assoc [level]) carrier' op' inst
    facts := facts.push (← lawOf s!"{labelPrefix}associativity of {description}" proof)
  if let some inst ← trySynthInstance? (mkApp2 (.const ``Std.IdempotentOp [level]) carrier op) then
    let instType ← instantiateMVars (← inferType inst)
    let #[carrier', op'] := instType.getAppArgs | throwError "unexpected IdempotentOp instance type"
    let proof := mkApp3 (.const ``Std.IdempotentOp.idempotent [level]) carrier' op' inst
    facts := facts.push (← lawOf s!"{labelPrefix}idempotence of {description}" proof)
  return facts

/-- Both identity laws of one operation for one concrete source unit.  Only a
term of the operation's carrier is tried; the synthesized instance supplies the
verified unit and its projections supply the two laws. -/
private def identityLawsOf (op unit : Expr) : MetaM (Array Auto.Lemma) := do
  let description := describeOp op
  let (carrier, level) ← carrierOf op
  let unitType ← instantiateMVars (← inferType unit)
  unless ← isDefEq unitType carrier do return #[]
  let some inst ← trySynthInstance? (mkApp3 (.const ``Std.LawfulIdentity [level]) carrier op unit)
    | trace[vampire] "Unit {unit} of {describeOp op} has no LawfulIdentity instance"
      return #[]
  let instType ← instantiateMVars (← inferType inst)
  let #[carrier', op', unit'] := instType.getAppArgs | throwError "unexpected LawfulIdentity instance type"
  let leftParent :=
    mkApp4 (.const ``Std.LawfulIdentity.toLawfulLeftIdentity [level]) carrier' op' unit' inst
  let left :=
    mkApp5 (.const ``Std.LawfulLeftIdentity.left_id [level, level]) carrier' carrier' op' unit' leftParent
  let rightParent :=
    mkApp4 (.const ``Std.LawfulIdentity.toLawfulRightIdentity [level]) carrier' op' unit' inst
  let right :=
    mkApp5 (.const ``Std.LawfulRightIdentity.right_id [level, level]) carrier' carrier' op' unit' rightParent
  return #[← lawOf s!"{labelPrefix}left identity {unit} of {description}" left,
    ← lawOf s!"{labelPrefix}right identity {unit} of {description}" right]

/-- Whether one of the collected facts already states this law verbatim or up to
definitional equality.  The structure fields of the caller's own instances often
state the very laws the synthesized instances project, and a second copy only
inflates the exported problem. -/
private def alreadyStated (candidate : Expr) (stated : Array Expr) : MetaM Bool := do
  if stated.any (candidate == ·) then return true
  for type in stated do
    if ← isDefEq candidate type then return true
  return false

/-- Discover `Std` law instances for the operations of the requested source.
Parameters must belong to the caller's context: binders opened temporarily
while walking a formula cannot escape into an exported law.  `stated` lists
the types of auxiliary facts that remain in the problem as axioms; laws they
already state are not duplicated.  The requested facts are deliberately not in
that baseline: the goal is negated, not kept, so a law it states is still
needed as an axiom. -/
def collect (sources : Array Auto.Lemma) (stated : Array Expr := #[]) :
    MetaM (Array Auto.Lemma) := do
  unless vampire.lawInstances.get (← getOptions) do return #[]
  let original ← getLCtx
  let mut operations : Array Expr := #[]
  let mut units : Array Expr := #[]
  for source in sources do
    if operations.size >= maxOperations && units.size >= maxUnits then break
    let sourceType ← instantiateMVars source.type
    -- Metavariables anywhere in a source fact make its anchor types unstable;
    -- skip it entirely rather than guessing around unknown positions.
    if sourceType.hasMVar then continue
    let state ← IO.mkRef {}
    scan original state sourceType
    let found ← state.get
    for op in found.operations do
      if operations.size >= maxOperations then break
      unless operations.contains op do operations := operations.push op
    for unit in found.units do
      if units.size >= maxUnits then break
      unless units.contains unit do units := units.push unit
  let mut facts : Array Auto.Lemma := #[]
  let mut stated := stated
  trace[vampire] "Law-instance anchors: {operations.size} operations [{",".intercalate (operations.map describeOp).toList}], {units.size} units [{",".intercalate (units.map describeTerm).toList}]"
  for op in operations do
    if facts.size >= maxFacts then break
    let saved ← saveState
    try
      for candidate in ← operationLawsOf op do
        if facts.size >= maxFacts then break
        unless ← alreadyStated candidate.type stated do
          facts := facts.push candidate
          stated := stated.push candidate.type
      for unit in units do
        if facts.size >= maxFacts then break
        for candidate in ← identityLawsOf op unit do
          if facts.size >= maxFacts then break
          unless ← alreadyStated candidate.type stated do
            facts := facts.push candidate
            stated := stated.push candidate.type
    catch _ => saved.restore
  trace[vampire] "Collected {facts.size} law-instance facts for {operations.size} source operations"
  return facts
end VampireHammer.Export.LawInstances

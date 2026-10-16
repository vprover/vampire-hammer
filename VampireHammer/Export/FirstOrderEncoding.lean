import Auto.Tactic
import VampireHammer.Options
import VampireHammer.Export.StructureProjections
import VampireHammer.Export.Inhabitation

/-!
Encode functions and propositions used as data through typed first-order
objects. Each object sort retains its actual Lean type in the atom valuation;
application symbols retain actual Lean application functions. Generated
definitions are checked Lean proofs, never unchecked exporter axioms.
-/

namespace VampireHammer.Export.FirstOrderEncoding

open Lean Meta Auto.Embedding.Lam

private structure Context where
  types : Std.HashMap Nat Expr
  terms : Std.HashMap Nat Expr
  termTypes : Array LamSort

private structure State where
  objectSorts : Std.HashMap LamSort LamSort := {}
  objects : Std.HashMap (LamTerm × List LamSort) LamTerm := {}
  applications : Std.HashMap (LamSort × LamSort) LamTerm := {}
  truth? : Option LamTerm := none
  definitions : Array LamTerm := #[]
  constructorHeads : Std.HashMap Nat Bool := {}
  constructors : Std.HashSet (LamTerm × List LamSort) := {}
  projections : Std.HashMap (Expr × LamSort) LamTerm := {}
  structureExtensionality : Std.HashSet (LamSort × Array Expr) := {}

private abbrev EncodeM := ReaderT Context (StateRefT State Auto.LamReif.ReifM)

private def expression (term : LamTerm) : EncodeM Expr := do
  let context ← read
  Auto.Lam2D.interpLamTermAsUnlifted context.types context.terms {} 0 term

/-- Function and proposition objects are new atomic sorts whose valuation is
the original Lean type. Scalar first-order domains keep their existing IDs. -/
private def objectSort (sort : LamSort) : EncodeM LamSort := do
  unless sort.isFunc || sort == .base .prop do return sort
  if let some result := (← get).objectSorts[sort]? then return result
  let (_, _, type, _) ← Auto.LamReif.updownFunc sort
  let result ← Auto.LamReif.newTypeExpr type
  modify fun state => { state with objectSorts := state.objectSorts.insert sort result }
  let witness? ← if sort == .base .prop then pure (some (mkConst ``True))
    else if let some (witness, _, _) := (← Auto.LamReif.getInhabitations)[sort]? then
      pure (some witness)
    else if let some index := (← read).termTypes.findIdx? (· == sort) then
      pure (← read).terms[index]?
    else if let .func domain range := sort then do
      let (_, _, domainType, _) ← Auto.LamReif.updownFunc domain
      if domain == range then
        pure (some (.lam `argument domainType (.bvar 0) .default))
      else if range == .base .prop then
        pure (some (.lam `argument domainType (mkConst ``True) .default))
      else if let some (witness, _, _) := (← Auto.LamReif.getInhabitations)[range]? then
        pure (some (.lam `argument domainType witness .default))
      else if vampire.onlyFacts.get (← getOptions) then pure none
      else Auto.Meta.trySynthInhabited type
    else pure none
  if let some witness := witness? then
    unless ← isDefEq (← inferType witness) type do
      throwError "invalid first-order object inhabitant"
    Auto.LamReif.newInhabitation witness (.leaf "first-order object inhabitation") result
  return result

/-- Register a symbol only after checking that its actual Lean value has the
type described by the encoded signature. Different first-order views of the
same Lean function may have distinct atom IDs. -/
private def atom (value : Expr) (sort : LamSort) : EncodeM LamTerm := do
  let (_, _, type, _) ← Auto.LamReif.updownFunc sort
  unless ← isDefEq (← inferType value) type do
    throwError "first-order encoding symbol has an inconsistent Lean type"
  let values ← Auto.LamReif.getVarVal
  Auto.LamReif.setVarVal (values.push (value, sort))
  if sort.isAtom then
    Auto.LamReif.newInhabitation value (.leaf "encoded source object inhabitation") sort
  return .atom values.size

private def truth : EncodeM LamTerm := do
  if let some result := (← get).truth? then return result
  let proposition := mkSort .zero
  let value := Expr.lam `proposition proposition (.bvar 0) .default
  let result ← atom value (.func (← objectSort (.base .prop)) (.base .prop))
  modify fun state => { state with truth? := some result }
  return result

private def holds (value : LamTerm) : EncodeM LamTerm := do
  return .app (← objectSort (.base .prop)) (← truth) value

private def application (domain range : LamSort) : EncodeM LamTerm := do
  if let some result := (← get).applications[(domain, range)]? then return result
  let (_, _, domainType, _) ← Auto.LamReif.updownFunc domain
  let (_, _, rangeType, _) ← Auto.LamReif.updownFunc range
  let functionType := mkForall `argument .default domainType rangeType
  let value := Expr.lam `function functionType
    (.lam `argument domainType (.app (.bvar 1) (.bvar 0)) .default) .default
  let result ← atom value (.func (← objectSort (.func domain range))
    (.func (← objectSort domain) (← objectSort range)))
  modify fun state => { state with applications := state.applications.insert (domain, range) result }
  return result

private def applyObject (domain range : LamSort) (function argument : LamTerm) :
    EncodeM LamTerm := do
  return .app (← objectSort domain)
    (.app (← objectSort (.func domain range)) (← application domain range) function) argument

private def interpretEncoded (term : LamTerm) : EncodeM Expr := do
  let types ← Auto.LamReif.getTyVal
  let values ← Auto.LamReif.getVarVal
  let typeMap := Std.HashMap.ofArray (types.zipIdx.map fun (entry, index) => (index, entry.1))
  let valueMap := Std.HashMap.ofArray (values.zipIdx.map fun (entry, index) => (index, entry.1))
  Auto.Lam2D.interpLamTermAsUnlifted typeMap valueMap {} 0 term

/-- Definitions must elaborate to actual reflexivity proofs. This validates
the encoding's indices and types before recording anything in the checker. -/
private def definition (term : LamTerm) : EncodeM Unit := do
  let type ← interpretEncoded term
  let proof ← forallTelescopeReducing type fun arguments body => do
    let goal ← mkFreshExprMVar body .syntheticOpaque
    try goal.mvarId!.refl
    catch _ =>
      let remaining ← goal.mvarId!.apply (mkConst ``Iff.rfl)
      unless remaining.isEmpty do throwError "first-order definition is not reflexive"
    mkLambdaFVars arguments (← instantiateMVars goal)
  unless ← isTypeCorrect proof do throwError "ill-typed first-order definition"
  Auto.LamReif.newAssertion proof (.leaf "first-order encoding definition") term
  modify fun state => { state with definitions := state.definitions.push term }

private def closeUniversals (bound : List LamSort) (term : LamTerm) : EncodeM LamTerm := do
  bound.foldlM (fun term sort => return term.mkForallEF (← objectSort sort)) term

private def splitApplication (term : LamTerm) : LamTerm × List LamTerm :=
  go term []
where
  go : LamTerm → List LamTerm → LamTerm × List LamTerm
    | .app _ function argument, arguments => go function (argument :: arguments)
    | head, arguments => (head, arguments)

/-- Eta-expand interpreted operations so their lifted function objects have
ordinary beta definitions ending in the original logical/arithmetic primitive. -/
private partial def etaExpand (sort : LamSort) (term : LamTerm) : LamTerm :=
  match sort with
  | .func domain range =>
    .lam domain (etaExpand range (.app domain term.bvarLift (.bvar 0)))
  | _ => term

mutual

private partial def formula (term : LamTerm) (bound : List LamSort := []) : EncodeM LamTerm := do
  let (head, arguments) := splitApplication term
  match head, arguments with
  | .base (.pcst .trueE), [] | .base (.pcst .falseE), [] => return term
  | .base (.pcst .not), [argument] =>
    return .app (.base .prop) head (← formula argument bound)
  | .base (.pcst connective), [left, right] =>
    return .app (.base .prop)
      (.app (.base .prop) (.base (.pcst connective)) (← formula left bound))
      (← formula right bound)
  | .base (.eq sort), [left, right] =>
    return LamTerm.mkEq (← objectSort sort) (← data sort left bound) (← data sort right bound)
  | .base (.forallE sort), [body] => quantifier true sort body bound
  | .base (.existE sort), [body] => quantifier false sort body bound
  | .base (.ncst constant), arguments =>
    let types := constant.lamCheck.getArgTys
    let values ← (types.zip arguments).mapM fun (type, value) => data type value bound
    return (types.zip values).foldl (fun term (type, value) => .app type term value) head
  | .base (.icst constant), arguments =>
    let types := constant.lamCheck.getArgTys
    let values ← (types.zip arguments).mapM fun (type, value) => data type value bound
    return (types.zip values).foldl (fun term (type, value) => .app type term value) head
  | _, _ => holds (← data (.base .prop) term bound)

private partial def quantifier (universal : Bool) (sort : LamSort) (body : LamTerm)
    (bound : List LamSort) : EncodeM LamTerm := do
  let body := match body with
    | .lam _ body => body
    | _ => .app sort body.bvarLift (.bvar 0)
  let encodedSort ← objectSort sort
  if encodedSort.isAtom && !(← Auto.LamReif.getRst).nonemptyMap.contains encodedSort then
    -- Retain this proposition without quantifying an uninhabited TF0 domain.
    -- Its valuation is the actual Lean proposition, and its truth definition
    -- is reflexive. No Nonempty assumption or domain element is invented.
    let original := if universal then body.mkForallEF sort else body.mkExistEF sort
    return ← holds (← liftedObject (.base .prop) original bound none)
  let encoded ← formula body (sort :: bound)
  let sort := encodedSort
  return if universal then encoded.mkForallEF sort else encoded.mkExistEF sort

private partial def data (sort : LamSort) (term : LamTerm)
    (bound : List LamSort) : EncodeM LamTerm := do
  match term with
  | .bvar _ => return term
  | .atom _ =>
    if (← objectSort sort) == sort then
      constructorDefinitions sort term bound term
      return term
    liftedObject sort term bound none
  | .etom _ => throwError "first-order encoding must precede Skolemization"
  | .lam .. => liftedObject sort term bound (some term)
  | _ =>
    let (head, arguments) := splitApplication term
    if let .base (.ite resultSort) := head then
      if let [condition, left, right] := arguments then
        let resultSort' ← objectSort resultSort
        let condition ← data (.base .prop) condition bound
        let left ← data resultSort left bound
        let right ← data resultSort right bound
        let condition ← holds condition
        return .app resultSort' (.app resultSort'
          (.app (.base .prop) (.base (.ite resultSort')) condition) left) right
    -- Proposition expressions used as objects need a truth definition; a
    -- predicate application instead uses the shared application operator.
    if sort == .base .prop then
      match head with
      | .base (.pcst _) | .base (.eq _) | .base (.forallE _) | .base (.existE _) =>
        return ← liftedObject sort term bound none
      | .base (.ncst _) | .base (.icst _) => return ← liftedObject sort term bound none
      | _ => pure ()
    match term with
    | .base (.ncst _) =>
      if sort == .base .nat then return term
      liftedObject sort term bound (some (etaExpand sort term))
    | .base (.icst _) =>
      if sort == .base .int then return term
      liftedObject sort term bound (some (etaExpand sort term))
    | .base _ => liftedObject sort term bound (some (etaExpand sort term))
    | .app domain function argument =>
      -- Keep fully applied Nat and Int primitives in their existing first-order
      -- representation so the checked arithmetic theory continues to apply.
      if let .base (.ncst constant) := head then
        if sort == .base .nat || sort == .base .prop then
          let argumentTypes := constant.lamCheck.getArgTys
          if arguments.length == argumentTypes.length then
            let encoded ← (argumentTypes.zip arguments).mapM fun (type, value) => data type value bound
            return (argumentTypes.zip encoded).foldl
              (fun term (type, value) => .app type term value) head
      if let .base (.icst constant) := head then
        if sort == .base .int || sort == .base .prop then
          let argumentTypes := constant.lamCheck.getArgTys
          if arguments.length == argumentTypes.length then
            let encoded ← (argumentTypes.zip arguments).mapM fun (type, value) => data type value bound
            return (argumentTypes.zip encoded).foldl
              (fun term (type, value) => .app type term value) head
      let encodedFunction ← data (.func domain sort) function bound
      let encodedArgument ← data domain argument bound
      let result ← applyObject domain sort encodedFunction encodedArgument
      constructorDefinitions sort term bound result
      return result
    | _ => throwError "unsupported first-order encoding object"

/-- Add checked projection equations only for source constructor applications.
They use the same function objects as explicit source projections, so congruence
can connect two constructor values without assuming an unverified datatype theory. -/
private partial def constructorDefinitions (sort : LamSort) (term : LamTerm)
    (bound : List LamSort) (encoded : LamTerm) : EncodeM Unit := do
  if vampire.onlyFacts.get (← getOptions) then return
  unless sort.isAtom do return
  let bound := if term.maxLooseBVarSucc == 0 then [] else bound
  let key := (term, bound)
  if (← get).constructors.contains key then return
  modify fun state => { state with constructors := state.constructors.insert key }
  let (head, arguments) := splitApplication term
  let .atom index := head | return
  let some functionSort := (← read).termTypes[index]? | return
  let domains := functionSort.getArgTys
  if arguments.length != domains.length then return
  let isConstructor ← if let some result := (← get).constructorHeads[index]? then pure result
    else do
      let result ← StructureProjections.isConstructor (← expression head)
      modify fun state => { state with constructorHeads := state.constructorHeads.insert index result }
      pure result
  unless isConstructor do return
  let close (term : LamTerm) := bound.foldl (fun term sort => .lam sort term) term
  let mut candidates ← (domains.zip arguments).toArray.mapM fun (sort, term) => do
    return (⟨sort, term, ← expression (close term)⟩ : StructureProjections.Argument)
  -- Dependent constructor parameters can already have been specialized by
  -- Auto. Their field values remain in the original source valuation even
  -- when they are absent from the remaining constructor argument list.
  for (sort, index) in (← read).termTypes.zipIdx do
    let term := LamTerm.atom index
    candidates := candidates.push ⟨sort, term, ← expression (close term)⟩
  let (_, _, structureType, _) ← Auto.LamReif.updownFunc sort
  let fields ← StructureProjections.collect structureType (← expression (close term)) candidates
  let mut equalities := #[]
  for field in fields do
    let signature := LamSort.func sort field.sort
    let symbol ← if let some symbol := (← get).projections[(field.value, signature)]? then pure symbol
      else do
        let mut originalSymbol? := none
        for (candidateSort, index) in (← read).termTypes.zipIdx do
          if candidateSort != signature then continue
          if ← withTransparency .all <| isDefEq (← expression (.atom index)) field.value then
            originalSymbol? := some (.atom index)
            break
        let symbol ← if let some original := originalSymbol? then data signature original []
          else atom field.value (← objectSort signature)
        modify fun state => { state with projections := state.projections.insert (field.value, signature) symbol }
        pure symbol
    let left ← applyObject sort field.sort symbol encoded
    let right ← data field.sort field.argument bound
    definition (← closeUniversals bound (LamTerm.mkEq (← objectSort field.sort) left right))
    let leftField ← applyObject sort field.sort symbol (.bvar 1)
    let rightField ← applyObject sort field.sort symbol (.bvar 0)
    equalities := equalities.push (LamTerm.mkEq (← objectSort field.sort) leftField rightField)
  let key := (sort, fields.map (·.value))
  unless (← get).structureExtensionality.contains key do
    modify fun state => { state with structureExtensionality := state.structureExtensionality.insert key }
    let conclusion := LamTerm.mkEq sort (.bvar 1) (.bvar 0)
    let statement ← closeUniversals [sort, sort] (equalities.foldr LamTerm.mkImp conclusion)
    if let some proof ← StructureProjections.proveExtensionality? (← interpretEncoded statement) then
      Auto.LamReif.newAssertion proof (.leaf "first-order encoding structure extensionality") statement
      modify fun state => { state with definitions := state.definitions.push statement }

private partial def liftedObject (sort : LamSort) (term : LamTerm)
    (bound : List LamSort) (definitionBody : Option LamTerm) : EncodeM LamTerm := do
  let bound := if term.maxLooseBVarSucc == 0 then [] else bound
  let key := (term, bound)
  if let some result := (← get).objects[key]? then return result
  let closed := bound.foldl (fun term sort => .lam sort term) term
  let value ← expression closed
  let resultSort ← objectSort sort
  let argumentSorts ← bound.reverse.mapM objectSort
  let signature := argumentSorts.foldr LamSort.func resultSort
  let symbol ← atom value signature
  let result := (argumentSorts.zip (List.range bound.length).reverse).foldl
    (fun term (sort, index) => .app sort term (.bvar index)) symbol
  modify fun state => { state with objects := state.objects.insert key result }
  if sort == .base .prop then
    let statement := LamTerm.mkIff (← holds result) (← formula term bound)
    definition (← closeUniversals bound statement)
  else if let some (.lam domain body) := definitionBody then
    let .func _ range := sort | throwError "lambda object has no function sort"
    let left ← applyObject domain range result.bvarLift (.bvar 0)
    let right ← data range body (domain :: bound)
    definition (← closeUniversals (domain :: bound)
      (LamTerm.mkEq (← objectSort range) left right))
  return result

end

/-- Extensionality connects equality of opaque function objects with equality
of their applications. Only inhabited argument domains can be quantified in
TF0; absence of a witness must never add a Nonempty assumption. -/
private def functionExtensionality : EncodeM Unit := do
  for ((domain, range), _) in (← get).applications.toArray do
    let encodedDomain ← objectSort domain
    unless (← Auto.LamReif.getInhabitations).contains encodedDomain do
      let (_, _, type, _) ← Auto.LamReif.updownFunc domain
      let some witness ← Auto.Meta.trySynthInhabited type | continue
      Auto.LamReif.newInhabitation witness
        (.leaf "first-order extensionality domain inhabitation") encodedDomain
    let functionSort := LamSort.func domain range
    let left ← applyObject domain range (.bvar 2) (.bvar 0)
    let right ← applyObject domain range (.bvar 1) (.bvar 0)
    let pointwise := (LamTerm.mkEq (← objectSort range) left right).mkForallEF encodedDomain
    let statement ← closeUniversals [functionSort, functionSort]
      (pointwise.mkImp (LamTerm.mkEq (← objectSort functionSort) (.bvar 1) (.bvar 0)))
    let type ← interpretEncoded statement
    let proof ← forallTelescopeReducing type fun arguments _ => do
      let [_, _, pointwise] := arguments.toList
        | throwError "invalid function extensionality encoding"
      mkLambdaFVars arguments (← mkAppM ``funext #[pointwise])
    unless ← isDefEq (← inferType proof) type do
      throwError "invalid function extensionality certificate"
    Auto.LamReif.newAssertion proof (.leaf "first-order encoding function extensionality") statement
    modify fun state => { state with definitions := state.definitions.push statement }

private partial def sourceWitnesses (proof : Expr) (term : LamTerm) :
    Auto.LamReif.ReifM Unit := do
  match splitApplication term with
  | (.base (.existE sort), [_]) =>
    let witness ← withTransparency .all <| mkAppM ``Exists.choose #[proof]
    Auto.LamReif.newInhabitation witness (.leaf "source existential witness") sort
  | (.base (.pcst .and), [left, right]) =>
    sourceWitnesses (← withTransparency .all <| mkAppM ``And.left #[proof]) left
    sourceWitnesses (← withTransparency .all <| mkAppM ``And.right #[proof]) right
  | _ => pure ()

/-- Reify all sources first, then encode them in one shared valuation. Source
proofs are retained and checked at the encoded formula type; no source fact
is accepted on the strength of an unchecked syntactic conversion. -/
def encodeFacts (sources : Array Auto.UMonoFact) : Auto.LamReif.ReifM (Array REntry) := do
  let original ← Auto.LamReif.reifFacts sources
  for (source, term) in sources.zip original do sourceWitnesses source.proof term
  VampireHammer.Export.Internal.deriveDomainInhabitants
  let types ← Auto.LamReif.getTyVal
  let terms ← Auto.LamReif.getVarVal
  let context : Context := {
    types := Std.HashMap.ofArray (types.zipIdx.map fun (entry, index) => (index, entry.1))
    terms := Std.HashMap.ofArray (terms.zipIdx.map fun (entry, index) => (index, entry.1))
    termTypes := terms.map Prod.snd }
  let action : EncodeM (Array REntry) := do
    -- Quantifying over proposition objects must retain the ordinary logical
    -- values True and False, with their checked truth definitions.
    let _ ← data (.base .prop) (.base .trueE) []
    let _ ← data (.base .prop) (.base .falseE) []
    let proposition ← objectSort (.base .prop)
    let equivalence := LamTerm.mkIff (← holds (.bvar 1)) (← holds (.bvar 0))
    let extensionality ← closeUniversals [.base .prop, .base .prop]
      (equivalence.mkImp (LamTerm.mkEq proposition (.bvar 1) (.bvar 0)))
    let actualType ← interpretEncoded extensionality
    let proof ← forallTelescopeReducing actualType fun arguments _ => do
      let [left, right, equivalent] := arguments.toList
        | throwError "invalid proposition extensionality encoding"
      mkLambdaFVars arguments (mkApp3 (mkConst ``propext) left right equivalent)
    unless ← isDefEq (← inferType proof) actualType do
      throwError "invalid proposition extensionality certificate"
    Auto.LamReif.newAssertion proof (.leaf "first-order encoding proposition extensionality") extensionality
    modify fun state => { state with definitions := state.definitions.push extensionality }
    let mut result := #[]
    for (source, original) in sources.zip original do
      let encoded ← formula original
      let actualType ← interpretEncoded encoded
      unless ← withTransparency .all <| isDefEq (← inferType source.proof) actualType do
        trace[vampire] "Encoding mismatch for {source.deriv}: original proof type {← inferType source.proof}; encoded type {actualType}; original term {original}; encoded term {encoded}"
        throwError "encoded source does not match its original Lean proof"
      Auto.LamReif.newAssertion source.proof source.deriv encoded
      result := result.push (.valid [] encoded)
    functionExtensionality
    return result ++ (← get).definitions.map (.valid [])
  Prod.fst <$> (action.run context).run {}

end VampireHammer.Export.FirstOrderEncoding

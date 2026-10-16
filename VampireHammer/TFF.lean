import Auto.Translation.LamUtils
import Auto.Embedding.LamBVarOp

namespace VampireHammer.TFF

open Auto.Embedding.Lam

/-- The TF0 problem and the reverse mappings that make replay possible.

The IDs refer to the lean-auto reification that produced this problem. Keep
that reification context alive when implementing reconstruction; these values
are a TPTP certificate interface, not Lean proofs. -/
structure Problem where
  /-- Native simply typed higher-order input uses THF syntax. -/
  higherOrder : Bool := false
  /-- Complete TF0 input sent to the external prover. -/
  text : String
  /-- Exported sort names paired with the lean-auto sorts they denote. -/
  sorts : Array (String × LamSort)
  /-- Exported function/predicate names paired with their original term and
  full first-order signature. -/
  symbols : Array (String × LamTerm × LamSort)
  /-- Exported input names paired with the source formula they represent. -/
  facts : Array (String × LamTerm)
  deriving Inhabited

/-- Immutable information collected from lean-auto before TF0 rendering. -/
private structure Context where
  /-- Sort of every ordinary atom ID. -/
  atomTypes : Array LamSort
  /-- Sort of every existential atom ID. -/
  etomTypes : Array LamSort
  /-- Sorts for which lean-auto has supplied a nonempty-domain proof. -/
  nonemptySorts : Array LamSort

/-- Tables and declaration lines accumulated as rendering discovers symbols. -/
private structure ExportState where
  /-- Reverse table for emitted TF0 sort names. -/
  sorts : Array (String × LamSort) := #[]
  /-- Reverse table for emitted TF0 symbols. -/
  symbols : Array (String × LamTerm × LamSort) := #[]
  /-- `tff(..., type, ...)` declarations, in discovery order. -/
  declarations : Array String := #[]

private abbrev ExportM := ReaderT Context (StateT ExportState (Except String))

private def fail (message : String) : ExportM α :=
  throw s!"TFF export: {message}"

/-- Ending of every export error that the checked function/proposition object
encoding can avoid. `prepareFirstOrderProblem` retries exactly these errors,
so the classification is made here, where each error is raised. -/
def objectEncodingSuffix : String := " (an object encoding is required)"

/-- Fail with an error that the object encoding can avoid. -/
private def failObjects (message : String) : ExportM α :=
  fail (message ++ objectEncodingSuffix)

/-- Register the TF0 name for an exported domain.

TF0 domains must be nonempty.  Uninterpreted Lean sorts therefore need
inhabitation evidence from lean-auto; the built-in Lean types `Nat` and `Int`
are already inhabited and receive uninterpreted TF0 sorts. -/
private def domain (s : LamSort) : ExportM String := do
  let name ← match s with
    | .atom n =>
      unless (← read).nonemptySorts.contains s do
        failObjects s!"sort s_a{n} has no known inhabitation evidence"
      pure s!"s_a{n}"
    -- `Nat` and `Int` are exported as *uninterpreted* TF0 sorts.  Their
    -- operations receive ordinary TPTP names below; their algebraic laws come
    -- from the checked `Std` law instances discovered for the source operations,
    -- never from a built-in theory.  This avoids Vampire's native arithmetic
    -- proof rules until they have dedicated reconstruction handlers.
    | .base .nat => pure "s_nat"
    | .base .int => pure "s_int"
    -- `Bool` is uninterpreted too; lean-auto's checked `boolFacts` state the
    -- meaning of its operations.
    | .base .bool => pure "s_bool"
    -- lean-auto reifies `Empty` as a base sort; it has no element.
    | .base .empty => fail "sort Empty has no known inhabitation evidence"
    | .func .. | .base .prop =>
      failObjects s!"unsupported domain {repr s}; expected an uninterpreted sort, Nat or Int"
    | _ => fail s!"unsupported domain {repr s}; expected an uninterpreted sort, Nat or Int"
  unless (← get).sorts.any (fun entry => entry.1 == name) do
    modify fun st => {st with sorts := st.sorts.push (name, s)}
  return name

private def signature : LamSort → List LamSort × LamSort
  | .func arg result =>
    let (args, result) := signature result
    (arg :: args, result)
  | s => ([], s)

private def symbol (head : LamTerm) : ExportM (String × LamSort) := do
  let (name, ty?) ← match head with
    | .atom n => pure (s!"t_a{n}", (← read).atomTypes[n]?)
    | .etom n => pure (s!"t_e{n}", (← read).etomTypes[n]?)
    -- Numeric constants and operations are declared as fresh TF0 symbols.
    -- They are mapped back to lean-auto's existing interpreted Nat terms by
    -- `TFF.Problem.symbols`; no new Lean constants are introduced in replay.
    | .base (.ncst constant) => pure (naturalName constant, some constant.lamCheck)
    -- Int operations are declared the same way and map back to lean-auto's
    -- interpreted Int terms.
    | .base (.icst constant) => pure (integerName constant, some constant.lamCheck)
    -- `Bool` operations are symbols as well. `ofProp` takes a proposition,
    -- which TF0 has only in the object encoding.
    | .base (.bcst .ofProp) =>
      failObjects "`Bool.ofProp` takes a proposition argument"
    | .base (.bcst constant) => pure (boolName constant, some constant.lamCheck)
    | .bvar _ | .base (.ite _) =>
      failObjects s!"unsupported application head {repr head}; higher-order terms and interpreted constants other than Nat and Int are not supported"
    | _ => fail s!"unsupported application head {repr head}; higher-order terms and interpreted constants other than Nat and Int are not supported"
  let some ty := ty? | fail s!"missing type for {name}"
  unless (← get).symbols.any (fun entry => entry.1 == name) do
    let (args, result) := signature ty
    let args ← args.mapM domain
    let result ← if result == .base .prop then pure "$o" else domain result
    let tyText := match args with
      | [] => result
      | [arg] => s!"({arg} > {result})"
      | _ => s!"(({String.intercalate " * " args}) > {result})"
    modify fun st => {st with
      symbols := st.symbols.push (name, head, ty)
      declarations := st.declarations.push s!"tff(type_{name}, type, {name}: {tyText})."}
  return (name, ty)
where
  naturalName : NatConst → String
    | .natVal n => s!"nat_{n}"
    | .nadd => "nat_add"
    | .nsub => "nat_sub"
    | .nmul => "nat_mul"
    | .ndiv => "nat_div"
    | .nmod => "nat_mod"
    | .nle => "nat_le"
    | .nlt => "nat_lt"
    | .nmax => "nat_max"
    | .nmin => "nat_min"
  boolName : BoolConst → String
    | .ofProp => "bool_ofProp"
    | .trueb => "bool_true"
    | .falseb => "bool_false"
    | .notb => "bool_not"
    | .andb => "bool_and"
    | .orb => "bool_or"
  integerName : IntConst → String
    | .iofNat => "int_ofNat"
    | .inegSucc => "int_negSucc"
    | .ineg => "int_neg"
    | .iabs => "int_abs"
    | .iadd => "int_add"
    | .isub => "int_sub"
    | .imul => "int_mul"
    | .idiv => "int_div"
    | .imod => "int_mod"
    | .iediv => "int_ediv"
    | .iemod => "int_emod"
    | .ile => "int_le"
    | .ilt => "int_lt"
    | .imax => "int_max"
    | .imin => "int_min"

private def splitApp : LamTerm → LamTerm × List LamTerm
  | .app _ fn arg =>
    let (head, args) := splitApp fn
    (head, args ++ [arg])
  | t => (t, [])

/-- Render with an expected type, rejecting partial applications and formulae
used as data. Only quantifier bodies may contain lambda abstraction. -/
private partial def render (expected : LamSort) (t : LamTerm)
    (bound : List LamSort := []) : ExportM String := do
  let prop := LamSort.base .prop
  let (head, args) := splitApp t
  if let .base (.ite result) := head then
    if let [condition, left, right] := args then
      unless result == expected do fail "conditional result type mismatch"
      if result != prop then discard <| domain result
      return s!"$ite({← render prop condition bound}, {← render result left bound}, {← render result right bound})"
  if expected == prop then
    match head, args with
    | .base (.pcst .trueE), [] => return "$true"
    | .base (.pcst .falseE), [] => return "$false"
    | .base (.pcst .not), [p] => return s!"(~ {← render prop p bound})"
    | .base (.pcst connective), [p, q] =>
      let op ← match connective with
        | .and => pure "&"
        | .or => pure "|"
        | .imp => pure "=>"
        | .iff => pure "<=>"
        | _ => fail "invalid logical connective application"
      return s!"({← render prop p bound} {op} {← render prop q bound})"
    | .base (.eq s), [lhs, rhs] =>
      if s == prop then
        return s!"({← render prop lhs bound} <=> {← render prop rhs bound})"
      let _ ← domain s
      return s!"({← render s lhs bound} = {← render s rhs bound})"
    | .base (.forallE s), [body] => return ← quantifier "!" s body
    | .base (.existE s), [body] => return ← quantifier "?" s body
    | _, _ => pure ()
  else
    let _ ← domain expected
  match t with
  | .bvar n =>
    let some ty := bound[n]? | fail s!"unbound variable {n}"
    unless ty == expected do fail "bound variable type mismatch"
    if ty == prop then failObjects "proposition-valued variables require an encoding beyond TF0"
    return s!"X{bound.length - n - 1}"
  | _ =>
    let (name, ty) ← symbol head
    let (argTypes, result) := signature ty
    unless result == expected do fail s!"result type mismatch for {name}"
    unless args.length == argTypes.length do
      fail s!"{name} must be fully applied (expected {argTypes.length} arguments, got {args.length})"
    let rendered ← (argTypes.zip args).mapM fun (ty, arg) => render ty arg bound
    return if rendered.isEmpty then name else s!"{name}({String.intercalate ", " rendered})"
where
  quantifier (q : String) (s : LamSort) (body : LamTerm) : ExportM String := do
    let sortName ← domain s
    let body ← match body with
      | .lam ty body =>
        unless ty == s do fail "quantifier binder type mismatch"
        pure body
      -- Eta-expand a predicate, shifting outer variables under the new binder.
      | _ => pure (.app s body.bvarLift (.bvar 0))
    return s!"({q} [X{bound.length}: {sortName}] : {← render (.base .prop) body (s :: bound)})"

/-- Check whether a single formula lies in the exported TF0 fragment, returning
the rendering error otherwise.  This lets callers discard optional facts before
`exportProblem` fixes the correspondence between TF0 inputs and lean-auto
entries. -/
def checkFact (atomTypes etomTypes nonemptySorts : Array LamSort)
    (fact : LamTerm) : Except String Unit := do
  let _ ← ((render (.base .prop) fact).run {atomTypes, etomTypes, nonemptySorts}).run {}

/-- Export monomorphic, many-sorted first-order logic with equality as TF0.
No facts are silently dropped. Original atom/etom and fact IDs are retained. -/
def exportProblem (atomTypes etomTypes nonemptySorts : Array LamSort)
    (facts : Array LamTerm) (negatedConjectures : Array Bool := #[]) : Except String Problem := do
  let action : ExportM (Array (String × LamTerm) × Array String) := do
    let mut entries := #[]
    let mut lines := #[]
    for (fact, i) in facts.zipIdx do
      let name := s!"fact{i}"
      -- `LamReif.preprocess` is responsible for lowering the first-order
      -- fragment before it reaches this exporter.  If a residual
      -- higher-order construct remains, retain both its post-preprocessing
      -- fact number and LamTerm in the diagnostic.  The fact number lines up
      -- with `trace.auto.lamReif.prep.printResult`, making it possible to
      -- distinguish a missing preprocessing conversion from an unsupported
      -- genuinely higher-order input.
      let formula ← try render (.base .prop) fact catch message =>
        fail s!"could not render post-preprocessing source {name}: {message}\nLamTerm: {repr fact}"
      entries := entries.push (name, fact)
      let role := if negatedConjectures[i]?.getD false then "negated_conjecture" else "axiom"
      lines := lines.push s!"tff({name}, {role}, {formula})."
    return (entries, lines)
  let ((entries, lines), st) ←
    (action.run {atomTypes, etomTypes, nonemptySorts}).run {}
  let sorts := st.sorts.map fun (name, _) => s!"tff(type_{name}, type, {name}: $tType)."
  let text := String.intercalate "\n" (sorts ++ st.declarations ++ lines).toList
  return {text, sorts := st.sorts, symbols := st.symbols, facts := entries}

end VampireHammer.TFF

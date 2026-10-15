import VampireHammer.TFF
import Auto.IR.TPTP_TH0

/-! Checked TH0 export with the same reverse signature as TF0 replay. Lean
`Bool` is deliberately not identified with `Prop`, and every atomic domain
retains the hammer's nonempty-domain check. -/

namespace VampireHammer.THF
open Auto.Embedding.Lam

private structure Context where
  atomTypes : Array LamSort
  etomTypes : Array LamSort
  nonemptySorts : Array LamSort

private structure State where
  sorts : Array (String × LamSort) := #[]
  symbols : Array (String × LamTerm × LamSort) := #[]
  declarations : Array String := #[]

private abbrev ExportM := ReaderT Context (StateT State (Except String))

private def fail (message : String) : ExportM α := throw s!"THF export: {message}"

private def renderSort (sort : LamSort) : ExportM String := do
  match sort with
  | .base .prop => pure "$o"
  | .func domain range => pure s!"({← renderSort domain} > {← renderSort range})"
  | .atom index =>
    unless (← read).nonemptySorts.contains sort do
      fail s!"sort s_a{index} has no known inhabitation evidence"
    register s!"s_a{index}" sort
  | .base .nat => register "s_nat" sort
  | .base .int => register "s_int" sort
  | .base .string => register "s_string" sort
  | .base (.bv width) => register s!"s_bv{width}" sort
  -- `Bool` is an uninterpreted sort; lean-auto's checked `boolFacts` state
  -- the meaning of its constants (see `symbol`).
  | .base .bool => register "s_bool" sort
  -- lean-auto reifies `Empty` as a base sort. It has no element, so the
  -- problem lacks a domain witness rather than using an unsupported domain.
  | .base .empty => fail "sort Empty has no known inhabitation evidence"
  | _ => fail s!"unsupported scalar domain {repr sort}"
where
  register name sort := do
    unless (← get).sorts.any (·.1 == name) do
      modify fun state => { state with sorts := state.sorts.push (name, sort) }
    pure name

private def boolName : BoolConst → String
  | .ofProp => "ofProp"
  | .trueb => "true"
  | .falseb => "false"
  | .notb => "not"
  | .andb => "and"
  | .orb => "or"

private def symbol (term : LamTerm) : ExportM (String × LamSort) := do
  let (name, sort?) ← match term with
    | .atom index => pure (s!"t_a{index}", (← read).atomTypes[index]?)
    | .etom index => pure (s!"t_e{index}", (← read).etomTypes[index]?)
    | .base (.ncst value) => pure (Auto.Lam2TH0.transNatConst value, some value.lamCheck)
    | .base (.icst value) => pure (Auto.Lam2TH0.transIntConst value, some value.lamCheck)
    -- `Bool.ofProp`, `true`, `false`, `!`, `&&` and `||` are uninterpreted
    -- symbols, as `ite` below. lean-auto adds its checked `boolFacts`
    -- (distinct values, the operations' equations, `ofProp p ↔ p`) whenever
    -- the problem uses `Bool`, and replay maps the symbols back.
    | .base (.bcst value) => pure (s!"t_bool_{boolName value}", some value.lamCheck)
    -- Scalar operations retain their checked Lean interpretation through the
    -- reverse signature. Export them as uninterpreted symbols: no arithmetic
    -- or string equations are assumed by the exporter.
    | .base base@(.scst _) | .base base@(.bvcst _) =>
      match (← get).symbols.find? (·.2.1 == term) with
      | some (name, _, sort) => pure (name, some sort)
      | none => pure (s!"t_scalar{(← get).symbols.size}", some (base.lamCheck default))
    -- `ite` at each sort is an uninterpreted symbol. lean-auto's checked
    -- `iteSpec` facts state its equations, and replay maps the symbol back
    -- to lean-auto's own `ite`.
    | .base (.ite sort) =>
      let symbols := (← get).symbols
      match symbols.find? (·.2.1 == term) with
      | some (name, _, sort) => pure (name, some sort)
      | none =>
        let count := symbols.foldl (init := 0) fun count entry =>
          if entry.2.1 matches .base (.ite _) then count + 1 else count
        pure (s!"t_ite{count}", some (.func (.base .prop) (.func sort (.func sort sort))))
    | _ => fail "unsupported THF symbol"
  let some sort := sort? | fail s!"missing type for `{name}`"
  unless (← get).symbols.any (·.1 == name) do
    let type ← renderSort sort
    modify fun state => { state with
      symbols := state.symbols.push (name, term, sort)
      declarations := state.declarations.push s!"thf(type_{name}, type, {name}: {type})." }
  pure (name, sort)

/-- Type-check while rendering: even application-domain annotations and bound
variable indices from a caller-supplied LamTerm are verified. -/
private partial def render (term : LamTerm) (bound : List LamSort := []) :
    ExportM (String × LamSort) := do
  match term with
  | .atom _ | .etom _ | .base (.ncst _) | .base (.icst _) | .base (.ite _) | .base (.bcst _) |
      .base (.scst _) | .base (.bvcst _) =>
    symbol term
  | .bvar index =>
    let some sort := bound[index]? | fail s!"unbound variable {index}"
    pure (s!"X{bound.length - index - 1}", sort)
  | .lam domain body =>
    let type ← renderSort domain
    let (body, range) ← render body (domain :: bound)
    pure (s!"(^ [X{bound.length}: {type}] : {body})", .func domain range)
  -- Applied quantifiers and equality are printed natively. Lean-auto's
  -- generic rendering of the constants reuses binder names at different
  -- types in nested scopes, which Vampire's sort checking rejects.
  | .app _ (.base (.forallE domain)) predicate => quantifier "!" domain predicate bound
  | .app _ (.base (.existE domain)) predicate => quantifier "?" domain predicate bound
  | .app _ (.app _ (.base (.eq domain)) lhs) rhs =>
    let (lhs, lhsSort) ← render lhs bound
    let (rhs, rhsSort) ← render rhs bound
    unless lhsSort == domain && rhsSort == domain do fail "equality argument type mismatch"
    discard <| renderSort domain
    pure (s!"({lhs} = {rhs})", .base .prop)
  | .app domain fn arg =>
    let (fn, fnSort) ← render fn bound
    let (arg, argSort) ← render arg bound
    let .func expected range := fnSort | fail "application head has no function type"
    unless domain == expected && argSort == expected do
      fail "application argument type mismatch"
    pure (s!"({fn} @ {arg})", range)
  | .base base =>
    match base with
    | .pcst _ | .eq _ | .forallE _ | .existE _ => pure ()
    | _ => fail s!"unsupported THF logical constant {repr base}"
    let sort := base.lamCheck default
    discard <| renderSort sort
    -- Unapplied constants are eta-expanded with depth-indexed binder names.
    let fresh := bound.length
    let text ← match base with
      | .pcst .iff => pure "(<=>)"
      | .forallE domain | .existE domain =>
        let quantifier := if base matches .forallE _ then "!" else "?"
        let type ← renderSort domain
        pure s!"(^ [X{fresh}: ({type} > $o)] : ({quantifier} [X{fresh + 1}: {type}] : \
          (X{fresh} @ X{fresh + 1})))"
      | .eq domain =>
        let type ← renderSort domain
        pure s!"(^ [X{fresh}: {type}, X{fresh + 1}: {type}] : (X{fresh} = X{fresh + 1}))"
      | _ =>
        match Auto.Lam2TH0.transLamBaseTerm base with
        | .ok text => pure text
        | .error error => fail error
    pure (text, sort)
where
  /-- A quantifier over a lambda binds its variable directly. Any other
  predicate is applied to a fresh variable, which cannot capture the
  predicate's own free variables `X0 .. X(n-1)`. -/
  quantifier (symbol : String) (domain : LamSort) (predicate : LamTerm)
      (bound : List LamSort) : ExportM (String × LamSort) := do
    let type ← renderSort domain
    let fresh := bound.length
    let body ← match predicate with
      | .lam domain' body =>
        unless domain' == domain do fail "quantifier domain mismatch"
        let (body, sort) ← render body (domain :: bound)
        unless sort == .base .prop do fail "quantifier body is not a proposition"
        pure body
      | _ =>
        let (text, sort) ← render predicate bound
        unless sort == .func domain (.base .prop) do fail "quantifier predicate type mismatch"
        pure s!"({text} @ X{fresh})"
    pure (s!"({symbol} [X{fresh}: {type}] : {body})", .base .prop)

def checkFact (atomTypes etomTypes nonemptySorts : Array LamSort)
    (fact : LamTerm) : Except String Unit := do
  let ((_, sort), _) ← ((render fact).run { atomTypes, etomTypes, nonemptySorts }).run {}
  unless sort == .base .prop do throw "THF export: source fact is not a proposition"

def exportProblem (atomTypes etomTypes nonemptySorts : Array LamSort)
    (facts : Array LamTerm) : Except String TFF.Problem := do
  let action : ExportM (Array (String × LamTerm) × Array String) := do
    let mut entries := #[]
    let mut lines := #[]
    for (fact, index) in facts.zipIdx do
      let name := s!"fact{index}"
      let (text, sort) ← render fact
      unless sort == .base .prop do fail s!"source `{name}` is not a proposition"
      entries := entries.push (name, fact)
      lines := lines.push s!"thf({name}, axiom, {text})."
    pure (entries, lines)
  let ((facts, lines), state) ← (action.run { atomTypes, etomTypes, nonemptySorts }).run {}
  let sorts := state.sorts.map fun (name, _) => s!"thf(type_{name}, type, {name}: $tType)."
  pure {
    higherOrder := true
    text := String.intercalate "\n" (sorts ++ state.declarations ++ lines).toList
    sorts := state.sorts
    symbols := state.symbols
    facts := facts }

end VampireHammer.THF

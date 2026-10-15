import VampireHammer.Replay.Term
import Tptp

/-!
Read-only decoding context, TPTP names, checked symbol lookup and application, and source
connective normalization.
-/

namespace VampireHammer.Replay.Decode.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal

def word : AtomicWord → Except String String
  | .lowerWord (.mk name) => .ok name
  | .singleQuoted (.mk name) => .ok name
  | .backQuoted _ => .error "back-quoted TPTP names are unsupported"

def nameToString : Tptp.Data.Name → Except String String
  | .atomicWord w => word w
  | .integer _ => .error "numeric TPTP names are unsupported"

def functor : Functor → Except String String
  | .mk w => word w

def constant : Constant → Except String String
  | .mk f => functor f

def definedFunctor : DefinedFunctor → Except String String
  | .mk (.mk (.mk name)) => .ok name

def varName : Variable → String
  | .mk (.mk name) => name

private def sortName : TffAtomicType → Except String String
  | .typeConstant (.mk (.mk w)) => word w
  | .tffAtomicType ty => sortName ty
  | _ => .error "unsupported TFF binder type"

/-- Information needed while decoding one parsed TFF formula.

`problem` is the exporter-side symbol table: its names map back to the
original lean-auto `LamTerm`s. `bound` is a de Bruijn environment whose head
is the most recently introduced TFF variable. -/
structure Context where
  /-- Exporter mappings that recover original lean-auto symbols by TPTP name. -/
  problem : TFF.Problem
  /-- Symbols declared by Vampire itself, principally Skolem functions. -/
  derivedSymbols : Array DerivedSymbol := #[]
  /-- Immutable indices built once for the complete proof, and shared when
  binder or formula settings change. Fold right to preserve first-match lookup
  and give exporter symbols priority over proof-local declarations. -/
  sortIndex : Std.HashMap String LamSort :=
    problem.sorts.foldr (fun (name, sort) index => index.insert name sort) {}
  symbolIndex : Std.HashMap String (LamTerm × LamSort) :=
    problem.symbols.foldr (fun (name, term, sort) index => index.insert name (term, sort))
      (derivedSymbols.foldr (fun symbol index => index.insert symbol.name (symbol.term, symbol.sort)) {})
  /-- Innermost-first TFF binder environment. `lookupBound` converts a name
  into the corresponding `LamTerm.bvar` index. -/
  bound : List (String × LamSort) := []
  /-- Decode an unparenthesized `a | b | c` chain as Lean's right-associated
  `a ∨ (b ∨ c)` rather than the parser's left-nested tree.  Used for formula
  (pre-CNF) steps, which VampLean's transformations reconstruct in Lean's
  grouping; explicit parentheses are always respected. Clause-phase steps keep
  the parser tree, whose binary grouping selects a resolution theorem. -/
  rightChains : Bool := false
  /-- Flatten nested conjunctions, including parenthesized ones, into the
  exporter's right-associated form. Used for source facts, which are compared
  with the exported hypotheses modulo grouping. Derived steps keep Vampire's
  explicit parentheses: preprocessing such as `ennf_transformation` prints
  `(a & b) & c`, and VampLean reconstructs exactly that grouping. -/
  flattenConjunctions : Bool := true

/-- Formula decoding is read-only: it needs the export mappings and binder
environment, and can fail with an explanatory parser-boundary error. -/
abbrev DecodeM := ReaderT Context (Except String)

def fail (message : String) : DecodeM α := throw message

/-- Attach a proof-node name to a decoder failure. Vampire proofs can contain
hundreds of formulas with similarly named variables; reporting the node here
makes a scoping or signature problem actionable without modifying the parser. -/
def inStep (name : String) (action : DecodeM α) : DecodeM α := do
  let context ← read
  match action.run context with
  | .ok result => pure result
  | .error message => fail s!"step `{name}`: {message}"

/-- Look up a declared TPTP sort in the exporter mapping. We never invent a
sort from Vampire output: accepting one would make later Lean translation
ambiguous. -/
def lookupSort (tffName : String) : DecodeM LamSort := do
  let some sort := (← read).sortIndex.get? tffName
    | fail s!"unknown TFF sort `{tffName}`"
  pure sort

/-- Recover the exact lean-auto symbol that was exported under `tffName`.
This is the key bridge that prevents a TPTP name such as `t_a3` from becoming a
new Lean constant during replay. -/
def lookupSymbol (tffName : String) : DecodeM (LamTerm × LamSort) := do
  let some symbol := (← read).symbolIndex.get? tffName
    | fail s!"unknown TFF symbol `{tffName}`"
  pure symbol

/-- Resolve a formula-local TPTP variable to a de Bruijn variable. The parser
uses names, but `LamTerm` is nameless; `findIdx?` is valid because `bound` is
stored innermost binder first. -/
def lookupBound (tffName : String) : DecodeM TypedTerm := do
  let some index := (← read).bound.findIdx? fun entry => entry.1 == tffName
    | fail s!"unbound TFF variable `{tffName}`"
  let sort := (← read).bound[index]!.2
  pure { term := .bvar index, sort }

/-- Rebuild a fully applied TFF application as a typed `LamTerm`.

TFF does not carry a type on each application node, so we consume the function
sort one argument at a time.  This catches malformed Vampire output at the
parser boundary, before it reaches Lean metaprogramming code. -/
def apply (head : LamTerm) (headSort : LamSort) (args : List TypedTerm) : DecodeM TypedTerm := do
  let mut term := head
  let mut sort := headSort
  for arg in args do
    let .func domain result := sort
      | fail "TFF application has too many arguments"
    unless domain == arg.sort do
      fail s!"TFF application type mismatch: expected {domain}, got {arg.sort}"
    term := .app domain term arg.term
    sort := result
  pure { term, sort }

private def decodeVariable : TffVariable → DecodeM (String × LamSort)
  | .tffTypedVariable (.mk var sort) => do
    pure (varName var, ← lookupSort (← sortName sort))
  | .variable var => fail s!"untyped TFF variable `{varName var}`"

def decodeVariables : TffVariableList → DecodeM (List (String × LamSort))
  | .tffVariable var => do pure [← decodeVariable var]
  | .tffVariableTffVariableList var rest => do
    let first ← decodeVariable var
    let rest ← decodeVariables rest
    pure (first :: rest)

/-- Normalize every disjunction in an input source fact, including those below
quantifier lambdas. This is never applied to a derived proof node. -/
private partial def normalizeSourceOrTerm : LamTerm → LamTerm
  | term@(.app _ (.app _ (.base .or) _) _) =>
    -- Normalize each disjunct once, rather than flattening and rebuilding
    -- every intermediate subtree of a long disjunction chain.
    (rightAssociate? .mkOr ((flattenOr term).map normalizeSourceOrTerm)).getD term
  | .lam sort body => .lam sort (normalizeSourceOrTerm body)
  | .app sort function argument =>
    .app sort (normalizeSourceOrTerm function) (normalizeSourceOrTerm argument)
  | term => term

def normalizeSourceOr (value : TypedTerm) : TypedTerm :=
  { value with term := normalizeSourceOrTerm value.term }

/-- Normalize an already type-checked conjunction without changing its sort. -/
def normalizeAnd (value : TypedTerm) : TypedTerm :=
  { value with term := (rightAssociate? .mkAnd (flattenAnd value.term)).getD value.term }

end VampireHammer.Replay.Decode.Internal

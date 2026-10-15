import VampireHammer.Replay.Decode.Context

/-!
Original binder metadata and nested AVATAR clause normalization. Binder names are retained
independently of the nameless formula.
-/

namespace VampireHammer.Replay.Decode.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal

/-! ### Original existential variable names

The parser retains the original names in ordinary outer-to-inner, left-to-right
syntax order. `LamTerm` erases these names, but it preserves the order of their
occurrences while normalizing connective association. The Skolem backend can
therefore label the original existential binders with this list, then recover
which leading prenex witness replaced each variable by matching occurrences.
We no longer simulate `simp` or assume an order for its quantifier lifting.
-/

private def rawVariableName : TffVariable → String
  | .tffTypedVariable (.mk namedVariable _) => varName namedVariable
  | .variable namedVariable => varName namedVariable

private def rawVariableNames : TffVariableList → Array String
  | .tffVariable namedVariable => #[rawVariableName namedVariable]
  | .tffVariableTffVariableList namedVariable rest =>
    #[rawVariableName namedVariable] ++ rawVariableNames rest

mutual

partial def existentialVariablesLogic : TffLogicFormula → Array String
  | .tffUnitaryFormula formula => existentialVariablesUnitary formula
  | .tffUnaryFormula formula => existentialVariablesUnary formula
  | .tffBinaryFormula (.tffBinaryAssoc (.tffAndFormula formula)) =>
    existentialVariablesAnd formula
  | .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula formula)) =>
    existentialVariablesOr formula
  | .tffBinaryFormula (.tffBinaryNonassoc (.mk left _ right)) =>
    existentialVariablesUnit left ++ existentialVariablesUnit right
  | _ => #[]

private partial def existentialVariablesUnitary : TffUnitaryFormula → Array String
  | .tffQuantifiedFormula (.mk quantifier variables body) =>
    let outer := match quantifier with
      | .fofQuantifier .question => rawVariableNames variables
      | _ => #[]
    outer ++ existentialVariablesUnit body
  | .tffLogicFormula formula => existentialVariablesLogic formula
  | _ => #[]

private partial def existentialVariablesPreunit : TffPreunitFormula → Array String
  | .tffUnitaryFormula formula => existentialVariablesUnitary formula
  | .tffPrefixUnary (.mk _ formula) => existentialVariablesPreunit formula

private partial def existentialVariablesUnary : TffUnaryFormula → Array String
  | .tffPrefixUnary (.mk _ formula) => existentialVariablesPreunit formula
  | _ => #[]

private partial def existentialVariablesUnit : TffUnitFormula → Array String
  | .tffUnitaryFormula formula => existentialVariablesUnitary formula
  | .tffUnaryFormula formula => existentialVariablesUnary formula
  | _ => #[]

private partial def existentialVariablesAnd : TffAndFormula → Array String
  | .tffUnitFormulaTffUnitFormula left right =>
    existentialVariablesUnit left ++ existentialVariablesUnit right
  | .tffAndFormulaTffUnitFormula left right =>
    existentialVariablesAnd left ++ existentialVariablesUnit right

private partial def existentialVariablesOr : TffOrFormula → Array String
  | .tffUnitFormulaTffUnitFormula left right =>
    existentialVariablesUnit left ++ existentialVariablesUnit right
  | .tffOrFormulaTffUnitFormula left right =>
    existentialVariablesOr left ++ existentialVariablesUnit right

end

/- Record the leading universal binders of a proof formula.

Vampire prints a long prefix in either of two equivalent concrete forms:
`! [X0, X1] : body` or `! [X0] : ! [X1] : body`. The C parser represents
the latter as nested `TffQuantifiedFormula`s, so collecting only the outer
block loses variables and makes otherwise identical preprocessing steps have
different Lean types. These mutually recursive helpers follow only that
leading chain; they intentionally stop before arbitrary formula connectives.

The full formula is decoded separately. Resolution needs this small parallel
view because Vampire's unifier names source variables (`X0`, `X1`, ...), while
the decoded body uses nameless de Bruijn indices. -/
mutual

partial def outerBinders (formula : TffLogicFormula) : DecodeM (Array FormulaBinder) :=
  match formula with
  | .tffUnitaryFormula (.tffQuantifiedFormula
      (.mk (.fofQuantifier .exclamation) variables body)) => do
    let variables ← decodeVariables variables
    let rest ← outerBindersInUnit body
    pure <| variables.toArray.map (fun (name, sort) => ⟨name, sort⟩) ++ rest
  | .tffUnitaryFormula (.tffLogicFormula formula) => outerBinders formula
  | _ => pure #[]

/-- Continue `outerBinders` through the unit-formula body of a quantifier. -/
private partial def outerBindersInUnit (formula : TffUnitFormula) :
    DecodeM (Array FormulaBinder) :=
  match formula with
  | .tffUnitaryFormula (.tffQuantifiedFormula
      (.mk (.fofQuantifier .exclamation) variables body)) => do
    let variables ← decodeVariables variables
    let rest ← outerBindersInUnit body
    pure <| variables.toArray.map (fun (name, sort) => ⟨name, sort⟩) ++ rest
  | .tffUnitaryFormula (.tffLogicFormula formula) => outerBinders formula
  | _ => pure #[]

end

 /-- Read the universal prefix on the component side of the standard AVATAR
definition spelling `spl ↔ component`.

The definition node itself has no outer binders: they occur only below the
right side of `↔`.  `LamTerm` correctly erases their names during ordinary
decoding, but Vampire's optional AVATAR-split certificate later refers to
them as `arg(definitionNode, variableName)`.  Retain this small parser-side
view so that the backend can resolve those references without guessing from
de Bruijn indices.  Vampire emits this orientation for `avatar_definition`;
an unexpected shape is represented by an empty prefix and makes the
certificate path decline safely. -/
partial def avatarDefinitionComponentBinders
    (formula : TffLogicFormula) : DecodeM (Array FormulaBinder) :=
  match formula with
  | .tffBinaryFormula (.tffBinaryNonassoc (.mk _ .iff component)) =>
    outerBindersInUnit component
  | .tffUnitaryFormula (.tffLogicFormula inner) =>
    avatarDefinitionComponentBinders inner
  | _ => pure #[]

/-! Vampire writes a quantified A-clause as

    `(! [X] : regularClause(X)) | avatarLiteral`

rather than putting the quantifier around the complete disjunction.  The
ordinary `outerBinders` view consequently sees no binders.  The following
small syntax traversal looks only through the top-level disjunction and its
parentheses and recovers the binders on that regular-clause disjunct.  It does
not descend into arbitrary literals or connectives. -/

mutual

private partial def nestedDisjunctBindersInUnit
    (formula : TffUnitFormula) : DecodeM (Option (Array FormulaBinder)) :=
  match formula with
  | .tffUnitaryFormula (.tffLogicFormula formula) => nestedDisjunctBinders formula
  | .tffUnitaryFormula (.tffQuantifiedFormula
      (.mk (.fofQuantifier .exclamation) variables _)) => do
    let variables ← decodeVariables variables
    pure <| some (variables.toArray.map fun (name, sort) => ⟨name, sort⟩)
  | _ => pure none

private partial def nestedDisjunctBindersInOr
    (formula : TffOrFormula) : DecodeM (Option (Array FormulaBinder)) :=
  match formula with
  | .tffUnitFormulaTffUnitFormula left right => do
    if let some binders ← nestedDisjunctBindersInUnit left then return some binders
    nestedDisjunctBindersInUnit right
  | .tffOrFormulaTffUnitFormula left right => do
    if let some binders ← nestedDisjunctBindersInOr left then return some binders
    nestedDisjunctBindersInUnit right

partial def nestedDisjunctBinders
    (formula : TffLogicFormula) : DecodeM (Option (Array FormulaBinder)) :=
  match formula with
  | .tffUnitaryFormula (.tffQuantifiedFormula
      (.mk (.fofQuantifier .exclamation) variables _)) => do
    let variables ← decodeVariables variables
    pure <| some (variables.toArray.map fun (name, sort) => ⟨name, sort⟩)
  | .tffUnitaryFormula (.tffLogicFormula formula) => nestedDisjunctBinders formula
  | .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula formula)) =>
    nestedDisjunctBindersInOr formula
  | _ => pure none

end

/-- Is this decoded term a positive or negative occurrence of an AVATAR atom? -/
private def isAvatarLamLiteral (atoms : Array LamTerm) (literal : LamTerm) : Bool :=
  atoms.contains literal ||
    match literal with
    | .app _ (.base .not) atom => atoms.contains atom
    | _ => false

/-- Right-associate a nonempty list of clause literals. -/
private def buildLamClause : List LamTerm → Option LamTerm
  | [] => none
  | [literal] => some literal
  | literal :: rest => LamTerm.mkOr literal <$> buildLamClause rest

/-- Convert Vampire's surface spelling of a quantified A-clause into the
internal spelling used by replay.

For example, `(∀ x, P x ∨ Q x) ∨ ¬ s` becomes
`∀ x, P x ∨ Q x ∨ ¬ s`.  This is the point where both halves become
explicit ordered literal lists: `decodeClausePhase` will later split the body
into `[P x, Q x]` and `[¬ s]`.  The transformation is used only when a direct
AVATAR literal is present and the parser found the matching quantified
disjunct. -/
def normalizeNestedAClause (decoded : TypedTerm)
    (nestedBinders? : Option (Array FormulaBinder)) : DecodeM (TypedTerm × Array FormulaBinder) := do
  let context ← read
  let avatarAtoms := context.derivedSymbols.filterMap fun symbol =>
    if symbol.kind == .avatarDefinition then some symbol.term else none
  let pieces := flattenOr decoded.term
  unless pieces.any (isAvatarLamLiteral avatarAtoms) do
    return (decoded, #[])
  let some binders := nestedBinders? | return (decoded, #[])
  let (avatar, regular) := pieces.partition (isAvatarLamLiteral avatarAtoms)
  -- A quantified regular component is one top-level disjunct in Vampire's
  -- syntax. Refuse to guess if a future output format distributes it across
  -- several disjuncts.
  let [quantifiedRegular] := regular | return (decoded, #[])
  let some regularBody := stripLeadingForalls binders.size quantifiedRegular
    | return (decoded, #[])
  let literals := flattenOr regularBody ++ avatar
  let some body := buildLamClause literals | return (decoded, #[])
  let normalized := binders.foldr (fun binder result =>
    LamTerm.mkForallEF binder.sort result) body
  pure (⟨normalized, .base .prop⟩, binders)

end VampireHammer.Replay.Decode.Internal

import VampireHammer.Preprocess.Metadata

/-!
Clause syntax, substitution, equality orientation, and occurrence-sensitive permutation checks.
-/

namespace VampireHammer.Preprocess.Internal

open Tptp.Data

/-! ## Clauses and AC nodes

TPTP represents a parenthesized right child of `|` as a unitary formula whose
content is another `TffLogicFormula`.  `flattenClause` follows those wrappers,
then `buildClause` creates an explicitly right-associated clause.  The latter
shape is exactly the useful surface form for the current textbook resolution
lemmas, while still denoting the same TPTP formula.
-/

mutual

partial def flattenClause : TffLogicFormula → Option (List TffUnitFormula)
  | .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula clause)) => flattenOr clause
  -- Parentheses around a whole clause are represented by this wrapper.  They
  -- carry no literal of their own, so look through them before treating the
  -- formula as a one-literal clause.
  | .tffUnitaryFormula (.tffLogicFormula formula) => flattenClause formula
  | formula => do pure [← asUnit? formula]

partial def flattenOr : TffOrFormula → Option (List TffUnitFormula)
  | .tffUnitFormulaTffUnitFormula left right => do
    let left ← flattenUnit left
    let right ← flattenUnit right
    pure (left ++ right)
  | .tffOrFormulaTffUnitFormula left right => do
    let left ← flattenOr left
    let right ← flattenUnit right
    pure (left ++ right)

partial def flattenUnit : TffUnitFormula → Option (List TffUnitFormula)
  | .tffUnitaryFormula (.tffLogicFormula formula) => flattenClause formula
  | formula => some [formula]

partial def asUnit? : TffLogicFormula → Option TffUnitFormula
  | .tffUnitaryFormula formula => some (.tffUnitaryFormula formula)
  | .tffUnaryFormula formula => some (.tffUnaryFormula formula)
  | .tffDefinedInfix formula => some (.tffDefinedInfix formula)
  | _ => none

end

def logicOfUnit : TffUnitFormula → TffLogicFormula
  | .tffUnitaryFormula formula => .tffUnitaryFormula formula
  | .tffUnaryFormula formula => .tffUnaryFormula formula
  | .tffDefinedInfix formula => .tffDefinedInfix formula

def unitOfLogic (formula : TffLogicFormula) : TffUnitFormula :=
  .tffUnitaryFormula (.tffLogicFormula formula)

def buildClause : List TffUnitFormula → Option TffLogicFormula
  | [] => none
  | [literal] => some (logicOfUnit literal)
  | literal :: rest => do
    let rest ← buildClause rest
    pure <| .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula
      (.tffUnitFormulaTffUnitFormula literal (unitOfLogic rest))))

/-! Applying a parsed resolution unifier

This is deliberately syntax-to-syntax substitution.  It is not a Lean term
translation and does not validate an inference; it simply lets preprocessing
ask what order the already-certified resolvent literals should have.  The
small supported fragment is the same first-order term fragment emitted by the
exporter: variables, constants, and fully-applied uninterpreted functions.
-/

private def lookupSubstitution (substitution : Substitution) (name : String) : Option TffTerm :=
  (substitution.find? fun binding => binding.1 == name).map Prod.snd

mutual

private partial def substArguments (substitution : Substitution) : TffArguments → Option TffArguments
  | .mk first rest => do
    let first ← substTerm substitution first
    let rest ← rest.mapM fun | .mk term => CommaTffTerm.mk <$> substTerm substitution term
    pure (.mk first rest)

private partial def substTerm (substitution : Substitution) : TffTerm → Option TffTerm
  | .tffLogicFormula formula => .tffLogicFormula <$> substLogic substitution formula
  | .definedTerm term => some (.definedTerm term)
  | .txfTuple _ => none

private partial def substPlain (substitution : Substitution) : TffPlainAtomic → Option TffPlainAtomic
  | .constant constant => some (.constant constant)
  | .functorTffArguments functor arguments =>
    .functorTffArguments functor <$> substArguments substitution arguments

private partial def substAtomic (substitution : Substitution) : TffAtomicFormula → Option TffAtomicFormula
  | .tffPlainAtomic atomic => .tffPlainAtomic <$> substPlain substitution atomic
  | .tffDefinedAtomic atomic => some (.tffDefinedAtomic atomic)
  | .tffSystemAtomic atomic => some (.tffSystemAtomic atomic)

private partial def substPreunit (substitution : Substitution) : TffPreunitFormula → Option TffPreunitFormula
  | .tffUnitaryFormula formula => .tffUnitaryFormula <$> substUnitary substitution formula
  | .tffPrefixUnary pref => .tffPrefixUnary <$> substPrefix substitution pref

private partial def substPrefix (substitution : Substitution) : TffPrefixUnary → Option TffPrefixUnary
  | .mk connective formula => .mk connective <$> substPreunit substitution formula

private partial def substUnitary (substitution : Substitution) : TffUnitaryFormula → Option TffUnitaryFormula
  | .tffQuantifiedFormula quantified => some (.tffQuantifiedFormula quantified)
  | .tffAtomicFormula atomic => .tffAtomicFormula <$> substAtomic substitution atomic
  | .txfUnitaryFormula (.mk boundVar) => do
    match lookupSubstitution substitution (variableText boundVar) with
    | none => pure (.txfUnitaryFormula (.mk boundVar))
    | some (.tffLogicFormula formula) => pure (.tffLogicFormula formula)
    | some _ => none
  | .tffLogicFormula formula => .tffLogicFormula <$> substLogic substitution formula

private partial def substUnit (substitution : Substitution) : TffUnitFormula → Option TffUnitFormula
  | .tffUnitaryFormula formula => .tffUnitaryFormula <$> substUnitary substitution formula
  | .tffUnaryFormula (.tffPrefixUnary pref) => do
    let pref ← substPrefix substitution pref
    pure (.tffUnaryFormula (.tffPrefixUnary pref))
  -- TPTP represents `left != right` separately from a prefix negation. It is
  -- common in equality-resolution parents, so substitute its two terms just
  -- as for a positive defined infix equality below.
  | .tffUnaryFormula (.tffInfixUnary (.mk left predicate right)) => do
    let left ← substUnitaryTerm substitution left
    let right ← substUnitaryTerm substitution right
    pure (.tffUnaryFormula (.tffInfixUnary (.mk left predicate right)))
  | .tffDefinedInfix (.mk left predicate right) =>
    .tffDefinedInfix <$> (.mk <$> substUnitaryTerm substitution left <*> pure predicate <*> substUnitaryTerm substitution right)

private partial def substUnitaryTerm (substitution : Substitution) : TffUnitaryTerm → Option TffUnitaryTerm
  | .tffAtomicFormula atomic => .tffAtomicFormula <$> substAtomic substitution atomic
  | .definedTerm term => some (.definedTerm term)
  | .txfTuple _ => none
  | .variable boundVar => do
    match lookupSubstitution substitution (variableText boundVar) with
    | none => pure (.variable boundVar)
    | some (.tffLogicFormula (.tffUnitaryFormula (.tffAtomicFormula atomic))) =>
      pure (.tffAtomicFormula atomic)
    | some _ => none
  | .tffLogicFormula formula => .tffLogicFormula <$> substLogic substitution formula

private partial def substOr (substitution : Substitution) : TffOrFormula → Option TffOrFormula
  | .tffUnitFormulaTffUnitFormula left right =>
    .tffUnitFormulaTffUnitFormula <$> substUnit substitution left <*> substUnit substitution right
  | .tffOrFormulaTffUnitFormula left right =>
    .tffOrFormulaTffUnitFormula <$> substOr substitution left <*> substUnit substitution right

partial def substLogic (substitution : Substitution) : TffLogicFormula → Option TffLogicFormula
  | .tffUnitaryFormula formula => .tffUnitaryFormula <$> substUnitary substitution formula
  | .tffUnaryFormula (.tffPrefixUnary pref) => do
    let pref ← substPrefix substitution pref
    pure (.tffUnaryFormula (.tffPrefixUnary pref))
  | .tffUnaryFormula (.tffInfixUnary (.mk left predicate right)) => do
    let left ← substUnitaryTerm substitution left
    let right ← substUnitaryTerm substitution right
    pure (.tffUnaryFormula (.tffInfixUnary (.mk left predicate right)))
  | .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula formula)) => do
    let formula ← substOr substitution formula
    pure (.tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula formula)))
  | .tffBinaryFormula _ => none
  | .tffDefinedInfix (.mk left predicate right) =>
    .tffDefinedInfix <$> (.mk <$> substUnitaryTerm substitution left <*> pure predicate <*> substUnitaryTerm substitution right)
  | _ => none

end

/-- Remove just the outer universal-clause wrapper from a parent. -/
partial def clauseBody : TffLogicFormula → Option TffLogicFormula
  | .tffUnitaryFormula (.tffLogicFormula formula) => clauseBody formula
  | .tffUnitaryFormula (.tffQuantifiedFormula (.mk _ _ (.tffUnitaryFormula (.tffLogicFormula body)))) => some body
  | formula => some formula

/-- Whether a clause has the leading quantified wrapper that `clauseBody`
removes. This is intentionally the same restricted surface shape as
`clauseBody`; it is used to avoid moving a body containing bound variables out
of their scope while constructing an optional preprocessing node. -/
partial def hasOuterClauseQuantifier : TffLogicFormula → Bool
  | .tffUnitaryFormula (.tffLogicFormula formula) => hasOuterClauseQuantifier formula
  | .tffUnitaryFormula (.tffQuantifiedFormula
      (.mk _ _ (.tffUnitaryFormula (.tffLogicFormula _)))) => true
  | _ => false

/-- Put a newly calculated clause body under exactly the quantifiers used by
Vampire's original resolvent. -/
partial def withClauseBody (original body : TffLogicFormula) : Option TffLogicFormula :=
  match original with
  | .tffUnitaryFormula (.tffLogicFormula formula) => do
    let result ← withClauseBody formula body
    pure (.tffUnitaryFormula (.tffLogicFormula result))
  | .tffUnitaryFormula (.tffQuantifiedFormula (.mk quantifier variables
      (.tffUnitaryFormula (.tffLogicFormula _)))) =>
    some (.tffUnitaryFormula (.tffQuantifiedFormula
      (.mk quantifier variables (.tffUnitaryFormula (.tffLogicFormula body)))))
  | _ => some body

def instantiatedTail (formula : TffLogicFormula) (selected : Nat)
    (substitution : Substitution) : Option (Option TffLogicFormula) := do
  let body ← clauseBody formula
  let literals ← flattenClause body
  guard (selected < literals.length)
  let tail := literals.take selected ++ literals.drop (selected + 1)
  match buildClause tail with
  | none => pure none
  | some tail => do
    let tail ← substLogic substitution tail
    pure (some tail)

/-- Form the textbook conclusion while retaining the two parent-tail groups.
For example, `(A ∨ (B ∨ C))` and `(¬A ∨ (D ∨ E))` produce
`(B ∨ C) ∨ (D ∨ E)`, rather than flattening it to a different association. -/
def resolutionConclusion (first second : Option TffLogicFormula) : Option TffLogicFormula :=
  match first, second with
  | some first, some second =>
    some (.tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula
      (.tffUnitFormulaTffUnitFormula (unitOfLogic first) (unitOfLogic second)))))
  | some formula, none | none, some formula => some formula
  | none, none => none -- unit/unit resolution has no corresponding theorem yet

/-- Equality is symmetric, and Vampire may orient an equality in the printed
resolvent differently from the parent tail calculated by this syntax pass.
The backend represents that change by an explicit `eq_comm` clause bridge;
here we only need to recognize it while calculating the occurrence mapping. -/
private def symmetricEquality (first second : TffUnitFormula) : Bool :=
  match first, second with
  | .tffDefinedInfix (.mk firstLeft firstConnective firstRight),
    .tffDefinedInfix (.mk secondLeft secondConnective secondRight) =>
    reprStr firstConnective == reprStr secondConnective &&
      reprStr firstLeft == reprStr secondRight &&
      reprStr firstRight == reprStr secondLeft
  -- Negative equality uses TPTP's distinct `TffInfixUnary` syntax for `!=`.
  -- Its connective is always inequality, so checking the reversed operands
  -- is sufficient and gives the parser-side counterpart of Lean's `ne_comm`.
  | .tffUnaryFormula (.tffInfixUnary (.mk firstLeft _ firstRight)),
    .tffUnaryFormula (.tffInfixUnary (.mk secondLeft _ secondRight)) =>
    reprStr firstLeft == reprStr secondRight &&
      reprStr firstRight == reprStr secondLeft
  | _, _ => false

/-- Match literals exactly or by equality symmetry.  No other logical
equivalence belongs to this parser-side reordering pass. -/
private def matchingLiteral (first second : TffUnitFormula) : Bool :=
  reprStr first == reprStr second || symmetricEquality first second

/-- Recognize the false literal eliminated by equality resolution after the
certificate's substitution has been applied.  TPTP prints this form as
`term != term`; it is structurally false, so no Lean-level simplification is
needed to identify it during this purely syntactic preprocessing pass. -/
def reflexiveDisequality (literal : TffUnitFormula) : Bool :=
  match literal with
  | .tffUnaryFormula (.tffInfixUnary (.mk left _ right)) =>
    reprStr left == reprStr right
  | _ => false

/-- Remove the first matching literal occurrence while retaining the original
source position. Consuming it matters for duplicate literals: `[A, B, A]`
reordered to `[A, A, B]` must produce `[0, 2, 1]`, rather than using source
position zero twice. -/
private def takeLiteralOccurrence (literal : TffUnitFormula) :
    List (Nat × TffUnitFormula) → Option (Nat × List (Nat × TffUnitFormula))
  | [] => none
  | (index, candidate) :: rest =>
    if matchingLiteral candidate literal then
      some (index, rest)
    else do
      let (found, remaining) ← takeLiteralOccurrence literal rest
      pure (found, (index, candidate) :: remaining)

/-- Return, for each target position, the source occurrence that supplies it.
The empty result denotes failure for a non-empty target; callers that need to
distinguish the empty clause also compare its length with the target length. -/
def literalPermutationIndices (source target : List TffUnitFormula) : List Nat :=
  let indexed := List.zipWith (fun literal index => (index, literal))
    source (List.range source.length)
  let rec collect (remaining : List (Nat × TffUnitFormula)) :
      List TffUnitFormula → Option (List Nat)
    | [] => some []
    | literal :: rest => do
      let (index, remaining) ← takeLiteralOccurrence literal remaining
      pure (index :: (← collect remaining rest))
  (collect indexed target).getD []

/-- The AC annotation records where every original output literal came from in
the textbook result. It is diagnostic data today, but makes the inserted node
usable by later syntax passes too. -/
def permutationTo (textbook original : TffLogicFormula) : List Nat :=
  match clauseBody textbook, clauseBody original with
  | some textbook, some original =>
    match flattenClause textbook, flattenClause original with
    | some textbook, some original =>
      literalPermutationIndices textbook original
    | _, _ => []
  | _, _ => []

mutual

private partial def literalTermKey : TffTerm → String
  | .tffLogicFormula formula => literalFormulaKey formula
  | .definedTerm term => reprStr term
  | .txfTuple tuple => reprStr tuple

private partial def literalArgumentsKey : TffArguments → String
  | .mk first rest =>
    String.intercalate "," <| literalTermKey first :: rest.map (fun | .mk term => literalTermKey term)

private partial def literalAtomicKey : TffAtomicFormula → String
  | .tffPlainAtomic (.constant (.mk (.mk word))) => wordText word
  | .tffPlainAtomic (.functorTffArguments (.mk word) arguments) =>
    s!"{wordText word}({literalArgumentsKey arguments})"
  | atomic => reprStr atomic

private partial def literalUnitaryTermKey : TffUnitaryTerm → String
  | .tffAtomicFormula atomic => literalAtomicKey atomic
  | .variable var => variableText var
  | .tffLogicFormula formula => literalFormulaKey formula
  | term => reprStr term

private partial def literalUnitaryKey : TffUnitaryFormula → String
  | .tffAtomicFormula atomic => literalAtomicKey atomic
  | .txfUnitaryFormula (.mk var) => variableText var
  | .tffLogicFormula formula => literalFormulaKey formula
  | unitary => reprStr unitary

private partial def literalPreunitKey : TffPreunitFormula → String
  | .tffUnitaryFormula unitary => literalUnitaryKey unitary
  | .tffPrefixUnary pref => literalPrefixKey pref

private partial def literalPrefixKey : TffPrefixUnary → String
  | .mk connective preunit => s!"{reprStr connective}({literalPreunitKey preunit})"

partial def literalUnitKey : TffUnitFormula → String
  | .tffUnitaryFormula unitary => literalUnitaryKey unitary
  | .tffUnaryFormula (.tffPrefixUnary pref) => literalPrefixKey pref
  | .tffDefinedInfix (.mk left connective right) =>
    s!"{literalUnitaryTermKey left}{reprStr connective}{literalUnitaryTermKey right}"
  | unit => reprStr unit

private partial def literalFormulaKey : TffLogicFormula → String
  | .tffUnitaryFormula unitary => literalUnitaryKey unitary
  | .tffUnaryFormula (.tffPrefixUnary pref) => literalPrefixKey pref
  | .tffDefinedInfix (.mk left connective right) =>
    s!"{literalUnitaryTermKey left}{reprStr connective}{literalUnitaryTermKey right}"
  | formula => reprStr formula

end

def hasLiteralPermutation (first second : TffLogicFormula) : Bool :=
  match clauseBody first, clauseBody second with
  | some first, some second =>
    match flattenClause first, flattenClause second with
    | some first, some second =>
      first.length == second.length &&
        !(List.zipWith (fun left right => literalUnitKey left == literalUnitKey right) first second).all id
    | _, _ => false
  | _, _ => false

def tffNode? : TptpInput → Option (String × FormulaRole × TffLogicFormula × Annotations)
  | .annotatedFormula (.tffAnnotated (.mk name role (.tffLogicFormula formula) annotations)) => do
    pure (← nameText? name, role, formula, annotations)
  | _ => none

end VampireHammer.Preprocess.Internal

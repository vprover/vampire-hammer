import VampireHammer.Preprocess.Avatar

/-!
Optional legacy clause normalization passes. Each pass retains proof parents and inserts
explicit AC nodes when the displayed literal order differs.
-/

namespace VampireHammer.Preprocess

open Tptp.Data
open Internal

/-- Legacy parser-AST A-clause normalization.

The live pipeline preserves Vampire's native spelling and lets `Replay` find
the nested quantifier while decoding.  This pass remains callable for older
experiments that require the quantifier to be syntactically outermost.
Annotations and DAG names are unchanged. -/
def normalizeAClauses : Pass := fun proof => do
  let .mk inputs := proof
  pure <| .mk <| inputs.map fun
    | .annotatedFormula (.tffAnnotated (.mk name role (.tffLogicFormula formula) annotations)) =>
      .annotatedFormula (.tffAnnotated (.mk name role
        (.tffLogicFormula (normalizeAClauseFormula formula)) annotations))
    | input => input

/-! ## The resolution-clause pass -/

private def freshName (used : Std.HashSet String) (base : String) : String :=
  -- The proof names come from Vampire and are finite.  A bounded search keeps
  -- this helper total while still making collisions practically impossible.
  match (List.range 10000).find? (fun suffix =>
    let candidate := if suffix == 0 then base else s!"{base}_{suffix}"
    !used.contains candidate) with
  | some suffix => if suffix == 0 then base else s!"{base}_{suffix}"
  | none => base ++ "_fresh"

/-- Compute equality resolution's natural clause body from one parent.

The parsed unifier is applied to the selected literal as well as to the
surviving tail. Exactly a reflexive disequality may be deleted. Returning
`none` for a unit refutation is intentional: an empty clause has no literal
order to normalize, so the backend can replay that original node directly. -/
private def equalityResolutionTail (parent : TffLogicFormula)
    (substitution : Substitution) : Option (Option TffLogicFormula) := do
  let body ← clauseBody parent
  let literals ← flattenClause body
  for index in [:literals.length] do
    let some literal := literals[index]? | continue
    let selected ← substLogic substitution (logicOfUnit literal)
    let selected ← asUnit? selected
    if reflexiveDisequality selected then
      return ← instantiatedTail parent index substitution
  none

/-- Insert a separate AC bridge for equality resolution when deleting the
instantiated `term != term` literal exposes a different clause order.

The equality-resolution theorem in the backend removes the false occurrence
and keeps the parent tail order. Vampire is free to print the surviving
literals in another order, but that order change is not part of equality
resolution itself. This pass makes the distinction explicit: the fresh core
uses the natural tail and the original node becomes an
`associativity_commutativity` proof step back to Vampire's spelling. -/
def equalityResolutionClauses : Pass := fun proof => do
  let .mk inputs := proof
  let mut formulas : Std.HashMap String TffLogicFormula := {}
  let mut used : Std.HashSet String := {}
  for input in inputs do
    if let some (name, _, formula, _) := tffNode? input then
      formulas := formulas.insert name formula
      used := used.insert name

  let mut output : List TptpInput := []
  for input in inputs do
    let some (stepName, role, original, annotations) := tffNode? input
      | output := output ++ [input]; continue
    let some (rule, details, proofParents, optional) := equalityResolutionRecord? annotations
      | output := output ++ [input]; continue
    let some [parentName] := parentNames proofParents
      | output := output ++ [input]; continue
    let some parentFormula := formulas.get? parentName
      | output := output ++ [input]; continue
    let textbook? : Option TffLogicFormula := do
      let substitutions ← substitutions? details
      let substitution ← substitutions.find? (fun (name, _) => name == parentName)
        |>.map Prod.snd
      let some body ← equalityResolutionTail parentFormula substitution
        | none
      withClauseBody original body
    match textbook? with
    | some textbook =>
      if hasRegularLiteralPermutation textbook original then
        -- The core keeps the original equality-resolution annotation and
        -- parent. Only its displayed formula changes to the natural tail.
        let coreName := freshName used s!"{stepName}_vh_equality_resolution"
        used := used.insert coreName
        formulas := formulas.insert coreName textbook
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName coreName) role (.tffLogicFormula textbook)
            (resolutionAnnotations rule details proofParents optional)))]
        output := output ++ [acNode stepName role original coreName
          (permutationTo textbook original)]
      else
        output := output ++ [input]
    | none => output := output ++ [input]
  pure (.mk output)

/-- Insert an output AC proof node only when a binary resolution's natural
tail-concatenation order differs from Vampire's displayed conclusion.

Resolution itself retains Vampire's original parent list and literal indices.
The list-clause resolution theorem accepts arbitrary positions, so moving a
selected parent literal to the head would only create redundant proof steps.
If a clause is not a supported `tff` disjunction, the pass leaves the original
node untouched; reconstruction can then use its normal fallback. -/
def resolutionClauses : Pass := fun proof => do
  let .mk inputs := proof
  let mut formulas : Std.HashMap String TffLogicFormula := {}
  let mut origins : Std.HashMap String (String × List Nat) := {}
  let mut used : Std.HashSet String := {}
  for input in inputs do
    if let some (name, _, formula, _) := tffNode? input then
      formulas := formulas.insert name formula
      used := used.insert name
    if let some (parent, permutation) := acOrigin? input then
      if let some (name, _, _, _) := tffNode? input then
        origins := origins.insert name (parent, permutation)

  let mut output : List TptpInput := []
  for input in inputs do
    let some (stepName, role, _formula, annotations) := tffNode? input
      | output := output ++ [input]; continue
    let some (rule, details, proofParents, optional) := resolutionRecord? annotations
      | output := output ++ [input]; continue
    let some actualParents := parentNames proofParents
      | output := output ++ [input]; continue
    let some reported := selections? details
      | output := output ++ [input]; continue
    -- Do not guess when Vampire did not give one selection per proof parent.
    if reported.length != actualParents.length then
      output := output ++ [input]
      continue

    let rewrittenParents := actualParents
    let mut rewrittenIndices := []
    for position in [:actualParents.length] do
      let parent := actualParents[position]!
      let some selection := reported[position]?
        | throw "internal preprocessing error: checked resolution selection disappeared"
      let index := positionAfterAc origins parent selection.reportedParent selection.index
      rewrittenIndices := rewrittenIndices ++ [index]

    let rewrittenDetails := rewriteResolutionDetails details rewrittenParents rewrittenIndices
    let rewrittenAnnotations := resolutionAnnotations rule rewrittenDetails (parents rewrittenParents) optional

    -- Resolve the syntactic parent tails after applying each parent-specific
    -- unifier.  The calculus backend has a soundness lemma for each polarity
    -- order (`Clause.resolve` and `Clause.resolveNegatedFirst`), so the core
    -- always preserves Vampire's proof-parent order.  This makes the parser
    -- pass independent of the selected literal's spelling and prevents an
    -- artificial AC node for a perfectly ordinary negative-first resolution.
    let textbook? : Option TffLogicFormula := do
      guard (rewrittenParents.length == 2)
      let substitutions ← substitutions? details
      guard (substitutions.length == 2)
      let firstFormula ← formulas.get? rewrittenParents[0]!
      let secondFormula ← formulas.get? rewrittenParents[1]!
      let first ← instantiatedTail firstFormula rewrittenIndices[0]! substitutions[0]!.2
      let second ← instantiatedTail secondFormula rewrittenIndices[1]! substitutions[1]!.2
      let body ← resolutionConclusion first second
      withClauseBody _formula body
    match textbook? with
    | some textbook =>
      if hasRegularLiteralPermutation textbook _formula then
        -- Keep Vampire's original name and output formula for all later DAG
        -- edges.  The freshly named resolution is the readable theorem-shaped
        -- core; this explicit AC node is its parser-level bridge back to the
        -- original proof certificate.
        let coreName := freshName used s!"{stepName}_vh_resolution"
        used := used.insert coreName
        formulas := formulas.insert coreName textbook
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName coreName) role (.tffLogicFormula textbook) rewrittenAnnotations))]
        output := output ++ [acNode stepName role _formula coreName (permutationTo textbook _formula)]
      else
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName stepName) role (.tffLogicFormula _formula) rewrittenAnnotations))]
    | none =>
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName stepName) role (.tffLogicFormula _formula) rewrittenAnnotations))]
  pure (.mk output)

/-- Insert an output AC proof node only when forward subsumption resolution
removes its selected literal and the remaining main-parent literals are not in
Vampire's displayed order.

Current Vampire certificates use `removed_literals(literal(main, index))`.
They intentionally omit the complementary side occurrence: replay finds it
by containment, while this syntax pass needs only the reported main position.
The natural A-clause conclusion consists of the main regular remainder and
the union of its AVATAR context with the side context. The backend interprets
that AVATAR part extensionally, so this pass inserts an AC node only when the
regular literal occurrences need reordering. -/
def forwardSubsumptionClauses : Pass := fun proof => do
  let .mk inputs := proof
  let mut formulas : Std.HashMap String TffLogicFormula := {}
  let mut origins : Std.HashMap String (String × List Nat) := {}
  let mut used : Std.HashSet String := {}
  for input in inputs do
    if let some (name, _, formula, _) := tffNode? input then
      formulas := formulas.insert name formula
      used := used.insert name
    if let some (parent, permutation) := acOrigin? input then
      if let some (name, _, _, _) := tffNode? input then
        origins := origins.insert name (parent, permutation)

  let mut output : List TptpInput := []
  for input in inputs do
    let some (stepName, role, original, annotations) := tffNode? input
      | output := output ++ [input]; continue
    let some (rule, details, proofParents, optional) := forwardSubsumptionRecord? annotations
      | output := output ++ [input]; continue
    let some actualParents := parentNames proofParents
      | output := output ++ [input]; continue
    let [mainParent, sideParent] := actualParents
      | output := output ++ [input]; continue
    let some reportedMain := removedLiteral? details
      | output := output ++ [input]; continue
    let mainIndex := positionAfterAc origins mainParent
      reportedMain.reportedParent reportedMain.index
    -- A pre-existing AC bridge changes the concrete parent name while the
    -- certificate can still mention its core. Rewrite explicit `subs` names
    -- by name, never by their array position: this rule is allowed to omit an
    -- empty main-parent substitution.
    let parentReplacements := actualParents.map fun actual =>
      let reported := (origins.get? actual).map Prod.fst |>.getD actual
      (reported, actual)
    let rewrittenDetails := rewriteForwardSubsumptionDetails details parentReplacements mainParent mainIndex
    let rewrittenAnnotations := resolutionAnnotations rule rewrittenDetails
      (parents [mainParent, sideParent]) optional
    let textbook? : Option TffLogicFormula := do
      let mainFormula ← formulas.get? mainParent
      let sideFormula ← formulas.get? sideParent
      -- Vampire can print an AVATAR component as
      -- `(forall X, clause(X)) ∨ ¬spl`. Its top-level formula has no
      -- leading binder even though the main first-order parent does. Reusing
      -- `original` as the wrapper in that case would move `clause(X)` outside
      -- the quantifier and manufacture free TFF variables. Decline this
      -- optional reordering; the backend can reconstruct the original node.
      guard (!hasOuterClauseQuantifier mainFormula ||
        hasOuterClauseQuantifier original)
      let substitutions := (substitutions? details).getD []
      let mainSubstitution := substitutions.find?
        (fun entry => entry.1 == reportedMain.reportedParent) |>.map Prod.snd |>.getD []
      let reportedSide := parentReplacements.find?
        (fun (_, actual) => actual == sideParent) |>.map Prod.fst |>.getD sideParent
      let sideSubstitution := substitutions.find?
        (fun entry => entry.1 == reportedSide) |>.map Prod.snd |>.getD []
      let mainRemainder ← instantiatedTail mainFormula mainIndex mainSubstitution
      let sideAvatar ← instantiatedAvatarPart sideFormula sideSubstitution
      let body ← resolutionConclusion mainRemainder sideAvatar
      withClauseBody original body
    match textbook? with
    | some textbook =>
      if hasRegularLiteralPermutation textbook original then
        let coreName := freshName used s!"{stepName}_vh_forward_subsumption_resolution"
        used := used.insert coreName
        formulas := formulas.insert coreName textbook
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName coreName) role (.tffLogicFormula textbook) rewrittenAnnotations))]
        output := output ++ [acNode stepName role original coreName (permutationTo textbook original)]
      else
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName stepName) role (.tffLogicFormula original) rewrittenAnnotations))]
    | none =>
      output := output ++ [.annotatedFormula (.tffAnnotated
        (.mk (lowerName stepName) role (.tffLogicFormula original) rewrittenAnnotations))]
  pure (.mk output)

/-- Search for the parent-order clause obtained by deleting only redundant
regular occurrences until it has the target multiplicity. At the base case we
require a complete occurrence-preserving match with the displayed target, so
the caller can safely add a separate AC bridge. -/
private partial def duplicateRemainder? (source target : List TffUnitFormula) :
    Option (List TffUnitFormula) := do
  if source.length == target.length then
    let permutation := literalPermutationIndices source target
    guard (permutation.length == target.length)
    return source
  guard (source.length > target.length)
  for removedIndex in [:source.length] do
    let some removed := source[removedIndex]? | continue
    if isAvatarSyntaxLiteral removed then continue
    let hasDuplicate := (List.range source.length).any fun candidateIndex =>
      candidateIndex != removedIndex &&
        source[candidateIndex]?.any
          (fun candidate => literalUnitKey candidate == literalUnitKey removed)
    unless hasDuplicate do continue
    let remainder := source.take removedIndex ++ source.drop (removedIndex + 1)
    if let some result := duplicateRemainder? remainder target then return result
  none

/-- Give duplicate contraction the same textbook/core separation as resolution.

Vampire does not report which duplicate occurrence it deleted and may print
the surviving literals in another order. This pass finds an occurrence whose
deletion leaves exactly the displayed multiset. The inserted core preserves
the parent's order and retains the original `duplicate_literal_removal`
annotation; a separate AC node restores a changed regular-literal order.
AVATAR literals are excluded as contraction candidates because first-order
inference rules operate only on the regular half of an A-clause, while their
AVATAR context already has set semantics. -/
def duplicateLiteralRemovalClauses : Pass := fun proof => do
  let .mk inputs := proof
  let mut formulas : Std.HashMap String TffLogicFormula := {}
  let mut used : Std.HashSet String := {}
  for input in inputs do
    if let some (name, _, formula, _) := tffNode? input then
      formulas := formulas.insert name formula
      used := used.insert name

  let mut output : List TptpInput := []
  for input in inputs do
    let some (stepName, role, original, annotations) := tffNode? input
      | output := output ++ [input]; continue
    let some proofParents := duplicateLiteralRemovalRecord? annotations
      | output := output ++ [input]; continue
    let some [parentName] := parentNames proofParents
      | output := output ++ [input]; continue
    let some parentFormula := formulas.get? parentName
      | output := output ++ [input]; continue
    let textbook? : Option TffLogicFormula := do
      let parentBody ← clauseBody parentFormula
      let parentLiterals ← flattenClause parentBody
      let targetBody ← clauseBody original
      let targetLiterals ← flattenClause targetBody
      let remainder ← duplicateRemainder? parentLiterals targetLiterals
      let body ← buildClause remainder
      withClauseBody original body
    match textbook? with
    | some textbook =>
      if hasLiteralPermutation textbook original then
        let coreName := freshName used s!"{stepName}_vh_duplicate_literal_removal"
        used := used.insert coreName
        formulas := formulas.insert coreName textbook
        output := output ++ [.annotatedFormula (.tffAnnotated
          (.mk (lowerName coreName) role (.tffLogicFormula textbook) annotations))]
        output := output ++
          [acNode stepName role original coreName (permutationTo textbook original)]
      else
        output := output ++ [input]
    | none => output := output ++ [input]
  pure (.mk output)

end VampireHammer.Preprocess

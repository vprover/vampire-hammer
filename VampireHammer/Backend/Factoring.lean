import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation

/-!
Ordinary factoring and duplicate literal removal.

Factoring preserves the order of retained regular occurrences; duplicate
removal also certifies any displayed permutation explicitly. Both lift their
proofs through `AClause.mapFirstOrder` when necessary. Certificate
decoding lives in `Backend.Metadata`; substitutions are shared with the other
calculus rules rather than reimplemented here.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Build the ground factoring proof after the parent clause has been
instantiated by Vampire's mgu. The reported index is the duplicate occurrence
to remove; the helper selects `Clause.factorLeft` or `Clause.factorRight` so
the output preserves exactly that occurrence order. -/
private def factorClause (parentProof : Expr) (literals target : Array Expr)
    (removedIndex : Nat) : MetaM (Option Expr) := do
  let some literal := literals[removedIndex]? | return none
  let mut duplicate? := none
  for index in [:literals.size] do
    if index != removedIndex then
      if ← isDefEq literal literals[index]! then
        duplicate? := some index
        break
  let some duplicateIndex := duplicate? | return none
  let expected := literals.take removedIndex ++ literals.drop (removedIndex + 1)
  let firstIndex := min removedIndex duplicateIndex
  let secondIndex := max removedIndex duplicateIndex
  let before := literals.toList.take firstIndex
  let between := (literals.toList.drop (firstIndex + 1)).take (secondIndex - firstIndex - 1)
  let after := literals.toList.drop (secondIndex + 1)
  let beforeList := mkPropList before
  let betweenList := mkPropList between
  let afterList := mkPropList after
  let core ← if removedIndex == secondIndex then
    mkAppM ``VampireHammer.Clause.factorRight
      #[literal, beforeList, betweenList, afterList, parentProof]
  else
    mkAppM ``VampireHammer.Clause.factorLeft
      #[literal, beforeList, betweenList, afterList, parentProof]
  normalizeRegularEqualityResult core expected target

/-- Reconstruct Vampire's basic one-parent factoring inference. The actual
proof is a ground duplicate contraction; mgu application happens first, so the
two literals are compared as ordinary Lean propositions. -/
def factoring (input : RuleInput) (info : FactoringInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 && input.parents.all (·.clauseForm) do
    return none
  let some onlyParent := input.parents[0]? | return none
  unless info.substitutions.size == 1 && info.removedLiteral.parent == onlyParent.parent.name do
    return none
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input info.substitutions targetBindings
      | return none
    let some parent := instantiated[0]? | return none
    let some view ← resolutionClauseView parent.1 parent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    trace[vampire.replay] "factoring {input.step.name}: remove {info.removedLiteral.parent}/{info.removedLiteral.index} from {view.regular.size} regular literal(s); carrying {view.avatar.size} AVATAR literal(s)"
    let reconstruct (candidate : ResolutionClauseView) : MetaM (Option Expr) :=
      mapRegularInference candidate targetRegular targetAvatar fun regularProof =>
        factorClause regularProof candidate.regular targetRegular info.removedLiteral.index
    -- The common case has literally duplicate propositions.  Keep it first so
    -- its generated term contains no needless `Clause.map` wrapper.
    let direct ← reconstruct view
    if direct.isSome then return direct
    -- Equality literals can be duplicates propositionally even when Vampire
    -- prints the occurrence being removed in the opposite orientation.  Make
    -- only that certificate-named occurrence match each possible companion;
    -- `orientRegularLiteralAt` accepts precisely equality/inequality symmetry.
    for duplicateIndex in [:view.regular.size] do
      if duplicateIndex == info.removedLiteral.index then continue
      let candidate ← Meta.withNewMCtxDepth do
        let some oriented ← orientRegularLiteralAt view info.removedLiteral.index
          view.regular[duplicateIndex]! | return none
        reconstruct oriented
      if candidate.isSome then
        trace[vampire.replay] "factoring {input.step.name}: oriented removed equality literal {info.removedLiteral.index} to match duplicate {duplicateIndex}"
        return candidate
    pure none

/-- Plan duplicate contraction before constructing any clause proofs.

Each target occurrence consumes a distinct source occurrence. Exact matches
use expression hashes; definitional aliases and equality symmetry use the
checked literal-equivalence fallback. Every deleted occurrence must match a
survivor. The final explicit permutation bridge handles Vampire's changed
literal order without sending an otherwise trivial contraction to `grind`. -/
def removeDuplicateClause (parentProof : Expr)
    (literals target : Array Expr) : MetaM (Option (Array Nat × Expr)) := do
  if literals.size < target.size then return none
  let mut occurrences : Std.HashMap Expr (Array Nat) := {}
  for index in [:literals.size] do
    occurrences := occurrences.insert literals[index]!
      ((occurrences.getD literals[index]! #[]).push index)
  let mut kept : Array Nat := #[]
  let mut keptSet : Std.HashSet Nat := {}
  for literal in target do
    let mut found? := (occurrences.getD literal #[]).find? (!keptSet.contains ·)
    if found?.isNone then
      for index in [:literals.size] do
        if keptSet.contains index then continue
        if (← literalEquivalent? literals[index]! literal).isSome then
          found? := some index
          break
    let some index := found? | return none
    kept := kept.push index
    keptSet := keptSet.insert index
  -- Check all deletions against survivors, rather than against another
  -- occurrence that might itself be deleted later.
  let mut retained : Std.HashMap Expr Nat := {}
  for index in kept do
    retained := retained.insert literals[index]! index
  let mut plan : Array (Nat × Nat) := #[]
  for index in [:literals.size] do
    if keptSet.contains index then continue
    let mut companion? := retained.get? literals[index]!
    if companion?.isNone then
      -- Expression hashes identify exact duplicates. Definitional equality
      -- and equality symmetry need the checked fallback comparison.
      for survivor in kept do
        if (← literalEquivalent? literals[index]! literals[survivor]!).isSome then
          companion? := some survivor
          break
      if let some companion := companion? then
        retained := retained.insert literals[index]! companion
    let some companion := companion? | return none
    plan := plan.push (index, companion)
  let mut proof := parentProof
  let mut current := literals
  let mut originalIndices := (Array.range literals.size)
  let mut removedIndices := #[]
  -- Delete right to left so earlier planned occurrence indices stay fixed.
  for (originalIndex, companion) in plan.reverse do
    let some removedIndex := originalIndices.findIdx? (· == originalIndex) | return none
    let some duplicateIndex := originalIndices.findIdx? (· == companion) | return none
    let oriented ← if ← isDefEq current[removedIndex]! current[duplicateIndex]! then
      pure (proof, current)
    else
      let some (orientedProof, orientedLiterals) ← orientLiteralAt proof
          current.toList removedIndex current[duplicateIndex]! | return none
      pure (orientedProof, orientedLiterals.toArray)
    let expected := current.take removedIndex ++ current.drop (removedIndex + 1)
    let some contracted ← factorClause oriented.1 oriented.2 expected removedIndex
      | return none
    proof := contracted
    current := expected
    originalIndices := originalIndices.take removedIndex ++ originalIndices.drop (removedIndex + 1)
    removedIndices := removedIndices.push removedIndex
  let some normalized ← reorderAndNormalize proof current.toList target.toList | return none
  return some (removedIndices, normalized)

/-- Instantiate the only parent with `substitution`, then contract duplicate
regular occurrences down to the displayed conclusion. For an A-clause only
the regular literal list is contracted. `AClause.mapFirstOrder` carries the
AVATAR list through literally unchanged. -/
private def contractDuplicates (input : RuleInput) (substitution : ParentSubstitution)
    (rule : String) : MetaM (Option Expr) :=
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input #[substitution] targetBindings
      | return none
    let some parent := instantiated[0]? | return none
    let some view ← resolutionClauseView parent.1 parent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    if view.isAClause then
      let regularType ← holdsType view.regular
      withLocalDeclD `duplicateRegular regularType fun regularProof => do
        let some (removedIndices, contracted) ←
            removeDuplicateClause regularProof view.regular targetRegular
          | return none
        let transform ← mkLambdaFVars #[regularProof] contracted
        let sourceList := mkPropList view.regular.toList
        let targetList := mkPropList targetRegular.toList
        let avatarList := mkPropList view.avatar.toList
        let core ← mkAppM ``VampireHammer.Clause.AClause.mapFirstOrder
          #[sourceList, targetList, avatarList, transform, view.proof]
        let some proof ← transportAvatarSet core targetRegular view.avatar targetAvatar
          | return none
        trace[vampire.replay] "{rule} {input.step.name}: contracted regular A-clause occurrence(s) {removedIndices.toList}; transported {view.avatar.size}/{targetAvatar.size} AVATAR set member(s)"
        pure (some proof)
    else
      unless targetAvatar.isEmpty do return none
      let some (removedIndices, proof) ←
          removeDuplicateClause view.proof view.regular targetRegular
        | return none
      trace[vampire.replay] "{rule} {input.step.name}: contracted clause occurrence(s) {removedIndices.toList}"
      pure (some proof)

/-- Reconstruct Vampire's annotation-free duplicate contraction. Parent
variables are instantiated by their identically named conclusion binders;
there is no unifier metadata on this rule. -/
def duplicateLiteralRemoval (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do
    return none
  let some onlyParent := input.parents[0]? | return none
  contractDuplicates input { parent := onlyParent.parent.name, bindings := #[] }
    "duplicate literal removal"

/-- Reconstruct `condensation`. Both of Vampire's engines remove one literal
that duplicates another after the certified substitution: general
condensation unifies two literals and instantiates the clause, fast
condensation binds only variables private to the removed literal. The
contraction is checked against the displayed conclusion, which for general
condensation starts with the surviving unified literal, as Vampire builds it. -/
def condensation (input : RuleInput) (info : FactoringInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do
    return none
  let some onlyParent := input.parents[0]? | return none
  let #[substitution] := info.substitutions | return none
  unless substitution.parent == onlyParent.parent.name &&
      info.removedLiteral.parent == onlyParent.parent.name do
    return none
  contractDuplicates input substitution "condensation"

end VampireHammer.Backend

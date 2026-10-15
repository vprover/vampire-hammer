import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation

/-!
Equality resolution, equality factoring, and trivial inequality removal.

The handlers work on instantiated literal lists and apply checked clause
lemmas. The common regular-clause adapter handles equality orientation and
AVATAR context, leaving this file responsible for the equality inference itself.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Reconstruct equality resolution after Vampire's mgu has made the selected
disequality reflexive. The removed occurrence is recovered from the instantiated
parent and checked against the complete child list, so no guessed position can
change the order or multiplicity of the remaining literals. -/
def equalityResolution (input : RuleInput) (info : EqualityResolutionInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) && info.substitutions.size == 1 do
    return none
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input info.substitutions targetBindings
      | return none
    let some parent := instantiated[0]? | return none
    let some view ← resolutionClauseView parent.1 parent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    for index in [:view.regular.size] do
      let literal := view.regular[index]!
      let some equation ← notArgument? literal | continue
      let some (_, left, right) := equation.eq? | continue
      unless ← isDefEq left right do continue
      let remainder := view.regular.take index ++ view.regular.drop (index + 1)
      let candidate ← mapRegularInference view targetRegular targetAvatar fun regularProof => do
        let before := mkPropList (view.regular.take index).toList
        let after := mkPropList (view.regular.drop (index + 1)).toList
        let core ← mkAppM ``VampireHammer.Clause.equalityResolve
          #[left, before, after, regularProof]
        normalizeRegularEqualityResult core remainder targetRegular
      if let some proof := candidate then
        trace[vampire.replay] "equality resolution {input.step.name}: removed reflexive disequality at regular literal {index}; carrying {view.avatar.size} AVATAR literal(s)"
        return some proof
    pure none

/-- Delete every reflexive disequality removed by Vampire's annotation-free
`trivial_inequality_removal` rule.

The rule is a simplifier rather than equality resolution: it carries no mgu,
and its parent and child use the same clause variables. We nevertheless
reconstruct it with the same small clause theorem. Searching the parent for a
reflexive `term ≠ term`, removing one occurrence, and recurring lets the
handler cover certificates which delete several trivial literals at once.
The base case checks the exact displayed child order (modulo equality
orientation only), so this helper cannot hide a literal permutation. -/
private partial def removeTrivialInequalitiesClause (parentProof : Expr)
    (literals target : Array Expr) : MetaM (Option (Array Nat × Expr)) := do
  if literals.size == target.size then
    let some normalized ← normalizeRegularEqualityResult parentProof literals target
      | return none
    return some (#[], normalized)
  if literals.size < target.size then return none
  for index in [:literals.size] do
    let literal := literals[index]!
    let some equation ← notArgument? literal | continue
    let some (_, left, right) := equation.eq? | continue
    unless ← isDefEq left right do continue
    let remainder := literals.take index ++ literals.drop (index + 1)
    let before := mkPropList (literals.take index).toList
    let after := mkPropList (literals.drop (index + 1)).toList
    let proof ← mkAppM ``VampireHammer.Clause.removeTrivialInequality
      #[left, before, after, parentProof]
    if let some (laterIndices, finalProof) ←
        removeTrivialInequalitiesClause proof remainder target then
      return some (#[index] ++ laterIndices, finalProof)
  pure none

/-- Reconstruct `trivial_inequality_removal` in the clause phase.

Unlike `equality_resolution`, Vampire does not report a unifier for this rule:
the displayed parent already contains the syntactically reflexive
disequality. `mapRegularInference` also makes the operation valid on the
first-order side of an A-clause while preserving its AVATAR context. -/
def trivialInequalityRemoval (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do
    return none
  let some onlyParent := input.parents[0]? | return none
  let substitution : ParentSubstitution :=
    { parent := onlyParent.parent.name, bindings := #[] }
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input #[substitution] targetBindings
      | return none
    let some parent := instantiated[0]? | return none
    let some view ← resolutionClauseView parent.1 parent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    let candidate ← mapRegularInference view targetRegular targetAvatar fun regularProof => do
      let some (removedIndices, resultProof) ←
          removeTrivialInequalitiesClause regularProof view.regular targetRegular
        | return none
      trace[vampire.replay] "trivial inequality removal {input.step.name}: removed reflexive regular literal(s) {removedIndices.toList}; carrying {view.avatar.size} AVATAR literal(s)"
      pure (some resultProof)
    pure candidate

/-- Build a function between two equality propositions when they are identical
or differ only by orientation. Equality factoring uses these functions to keep
the actual parent spelling visible while reasoning with a common left side. -/
private def equalityConversion (source target : Expr) : MetaM (Option Expr) := do
  let sourceWhnf ← whnf source
  let targetWhnf ← whnf target
  let some (_, sourceLeft, sourceRight) := sourceWhnf.eq? | return none
  let some (_, targetLeft, targetRight) := targetWhnf.eq? | return none
  let direct ← isDefEq sourceLeft targetLeft
  let directRight ← if direct then isDefEq sourceRight targetRight else pure false
  let reverse ← if directRight then pure false else isDefEq sourceLeft targetRight
  let reverseRight ← if reverse then isDefEq sourceRight targetLeft else pure false
  unless directRight || reverseRight do return none
  withLocalDeclD `equalityOrientation source fun proof => do
    let result ← if directRight then pure proof else mkAppM ``Eq.symm #[proof]
    some <$> mkLambdaFVars #[proof] result

/-- Build `selectedRight ≠ retainedRight → difference`, accepting Vampire's
canonical printing of the derived disequality in either orientation. -/
private def disequalityConversion (selectedRight retainedRight difference : Expr) :
    MetaM (Option Expr) := do
  let source ← mkAppM ``Ne #[selectedRight, retainedRight]
  let some targetEquation ← notArgument? difference | return none
  let some (_, targetLeft, targetRight) := targetEquation.eq? | return none
  let direct ← isDefEq selectedRight targetLeft
  let directRight ← if direct then isDefEq retainedRight targetRight else pure false
  let reverse ← if directRight then pure false else isDefEq selectedRight targetRight
  let reverseRight ← if reverse then isDefEq retainedRight targetLeft else pure false
  unless directRight || reverseRight do return none
  withLocalDeclD `factoringDifference source fun proof => do
    let result ← if directRight then pure proof else mkAppM ``Ne.symm #[proof]
    some <$> mkLambdaFVars #[proof] result

/-- Apply the equality-factoring clause theorem to one instantiated candidate pair.
The selected equality is removed, the retained equality stays at its original
position, and Vampire's derived disequality is placed first. -/
private def equalityFactorCandidate (parentProof : Expr) (literals target : Array Expr)
    (selectedIndex retainedIndex : Nat) : MetaM (Option Expr) := do
  if selectedIndex == retainedIndex || target.size != literals.size || target.isEmpty then
    return none
  let selectedLiteral := literals[selectedIndex]!
  let retainedLiteral := literals[retainedIndex]!
  let selected ← whnf selectedLiteral
  let retained ← whnf retainedLiteral
  let some (_, selectedLeft, selectedRight0) := selected.eq? | return none
  let some (_, retainedLeft, retainedRight0) := retained.eq? | return none
  let difference := target[0]!
  let selectedOrientations := #[(selectedLeft, selectedRight0), (selectedRight0, selectedLeft)]
  let retainedOrientations := #[(retainedLeft, retainedRight0), (retainedRight0, retainedLeft)]
  for (common, selectedRight) in selectedOrientations do
    let selectedEquation ← mkAppM ``Eq #[common, selectedRight]
    let some selectedToCommon ← equalityConversion selectedLiteral selectedEquation | continue
    for (retainedCommon, retainedRight) in retainedOrientations do
      unless ← isDefEq common retainedCommon do continue
      let retainedEquation ← mkAppM ``Eq #[common, retainedRight]
      let some retainedFromCommon ← equalityConversion retainedEquation retainedLiteral | continue
      let some differenceProof ← disequalityConversion selectedRight retainedRight difference
        | continue
      if selectedIndex < retainedIndex then
        let before := literals.take selectedIndex
        let between := (literals.drop (selectedIndex + 1)).take
          (retainedIndex - selectedIndex - 1)
        let after := literals.drop (retainedIndex + 1)
        let beforeList := mkPropList before.toList
        let betweenList := mkPropList between.toList
        let afterList := mkPropList after.toList
        let core ← mkAppM ``VampireHammer.Clause.equalityFactorLeft
          #[common, selectedRight, retainedRight, difference,
            selectedLiteral, retainedLiteral, beforeList, betweenList, afterList,
            selectedToCommon, retainedFromCommon, differenceProof, parentProof]
        let natural := #[difference] ++ before ++ between ++ #[retainedLiteral] ++ after
        return ← normalizeRegularEqualityResult core natural target
      else
        let before := literals.take retainedIndex
        let between := (literals.drop (retainedIndex + 1)).take
          (selectedIndex - retainedIndex - 1)
        let after := literals.drop (selectedIndex + 1)
        let beforeList := mkPropList before.toList
        let betweenList := mkPropList between.toList
        let afterList := mkPropList after.toList
        let core ← mkAppM ``VampireHammer.Clause.equalityFactorRight
          #[common, selectedRight, retainedRight, difference,
            selectedLiteral, retainedLiteral, beforeList, betweenList, afterList,
            selectedToCommon, retainedFromCommon, differenceProof, parentProof]
        let natural := #[difference] ++ before ++ #[retainedLiteral] ++ between ++ after
        return ← normalizeRegularEqualityResult core natural target
  pure none

/-- Reconstruct equality factoring by applying the recorded mgu, then searching
the instantiated parent for the selected/retained positive-equality pair whose
transitivity conclusion is exactly Vampire's child clause. -/
def equalityFactoring (input : RuleInput) (info : EqualityFactoringInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) && info.substitutions.size == 1 do
    return none
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input info.substitutions targetBindings
      | return none
    let some parent := instantiated[0]? | return none
    let some view ← resolutionClauseView parent.1 parent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    for selectedIndex in [:view.regular.size] do
      for retainedIndex in [:view.regular.size] do
        let candidate ← Meta.withNewMCtxDepth <|
          mapRegularInference view targetRegular targetAvatar fun regularProof =>
            equalityFactorCandidate regularProof view.regular targetRegular
              selectedIndex retainedIndex
        if let some proof := candidate then
          trace[vampire.replay] "equality factoring {input.step.name}: removed regular equality {selectedIndex}, retained equality {retainedIndex}; carrying {view.avatar.size} AVATAR literal(s)"
          return some proof
    pure none

end VampireHammer.Backend

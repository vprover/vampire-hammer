import VampireHammer.Backend.Metadata
import VampireHammer.Backend.Common
import VampireHammer.Backend.Congruence
import VampireHammer.Backend.Instantiation

/-!
Binary resolution and its variants (extensionality resolution, forward literal
rewriting, unit-resulting and constrained resolution), and forward/backward
subsumption resolution.

Both handlers instantiate parents through `Backend.Instantiation`, inspect the
selected literal occurrences, and apply clause soundness lemmas. They operate
on the regular half of A-clauses and carry the AVATAR context separately.
The displayed regular order is checked without silently permuting it.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Build one clause-form binary-resolution proof from Vampire's certificate.

* `positive` and `negative` are the instantiated parent clauses, after their
  recorded substitutions. Their regular lists are the flattened literal
  occurrences in Vampire's left-to-right order; duplicates are retained
  because indices address occurrences.
* The literal at `positiveIndex` is `atom`; the literal at `negativeIndex`
  is syntactically `¬ atom` (the caller orients it first).
* `negativeFirst` records that Vampire's first parent supplies the negative
  literal. It selects the named soundness theorem (`resolve` or
  `resolveNegatedFirst`), so the generated term states the parent order
  directly instead of proving an implicit permutation.

The theorem removes the two selected occurrences and concatenates the
remaining regular lists in parent order. When either parent is an A-clause,
the `AClause` variants carry both AVATAR lists without inspecting them; an
ordinary parent is embedded with an empty AVATAR list. A parser-side
preprocessing pass inserts a separate `associativity_commutativity` node when
Vampire displays the resolvent in a different order, so resolution itself
contains no permutation logic. -/
private def buildResolution (positive negative : ResolutionClauseView)
    (positiveIndex negativeIndex : Nat) (atom : Expr) (negativeFirst : Bool)
    (targetRegular targetAvatar : Array Expr) : MetaM (Option Expr) := do
  let positiveSides := (positive.regular.take positiveIndex, positive.regular.drop (positiveIndex + 1))
  let negativeSides := (negative.regular.take negativeIndex, negative.regular.drop (negativeIndex + 1))
  let (first, second, (firstBefore, firstAfter), (secondBefore, secondAfter)) :=
    if negativeFirst then (negative, positive, negativeSides, positiveSides)
    else (positive, negative, positiveSides, negativeSides)
  let resultRegular := (firstBefore ++ firstAfter) ++ (secondBefore ++ secondAfter)
  let sideLists := #[firstBefore, firstAfter, secondBefore, secondAfter].map fun side =>
    mkPropList side.toList
  if !positive.isAClause && !negative.isAClause then
    let rule := if negativeFirst then ``VampireHammer.Clause.resolveNegatedFirst
      else ``VampireHammer.Clause.resolve
    let core := mkAppN (mkConst rule) (#[atom] ++ sideLists ++ #[first.proof, second.proof])
    return ← normalizeClauseResult core resultRegular #[] targetRegular #[] false
  let asAClause (view : ResolutionClauseView) : MetaM Expr := do
    if view.isAClause then return view.proof
    let regularList := mkPropList view.regular.toList
    mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[regularList, view.proof]
  let avatarLists := #[first.avatar, second.avatar].map fun avatar =>
    mkPropList avatar.toList
  let rule := if negativeFirst then ``VampireHammer.Clause.AClause.resolveNegatedFirst
    else ``VampireHammer.Clause.AClause.resolve
  let core := mkAppN (mkConst rule)
    (#[atom] ++ sideLists ++ avatarLists ++ #[← asAClause first, ← asAClause second])
  normalizeClauseResult core resultRegular (first.avatar ++ second.avatar)
    targetRegular targetAvatar true

/-- Resolve once the negative selected literal is known to be `¬ negativeAtom`.

The calculus theorem needs selected literals literally shaped as `L` and
`¬L`.  If Vampire prints an equality below the negative literal in the other
orientation, the common occurrence-level bridge `orientRegularLiteralAt`
rewrites just that one parent literal (e.g. `¬(a = b)` to `¬(b = a)`) before
the theorem is applied, retaining all other regular and AVATAR literals. -/
private def resolveOriented (positive negative : ResolutionClauseView)
    (positiveIndex negativeIndex : Nat) (negativeAtom : Expr) (negativeFirst : Bool)
    (targetRegular targetAvatar : Array Expr) : MetaM (Option Expr) := do
  let some positiveLiteral := positive.regular[positiveIndex]? | return none
  let (negative, atom) ← if ← isDefEq positiveLiteral negativeAtom then
    -- Keep the first parent's spelling of the atom.
    pure (negative, if negativeFirst then negativeAtom else positiveLiteral)
  else
    let some oriented ← orientRegularLiteralAt negative negativeIndex
        (mkApp (mkConst ``Not) positiveLiteral) | return none
    pure (oriented, positiveLiteral)
  buildResolution positive negative positiveIndex negativeIndex atom negativeFirst
    targetRegular targetAvatar

/-- Resolve `first` at `firstIndex` against `second` at `secondIndex`, in
Vampire's parent order: first as the positive parent, otherwise first as the
negative one. Each attempt runs in its own metavariable context. -/
private def resolveViews (first second : ResolutionClauseView) (firstIndex secondIndex : Nat)
    (targetRegular targetAvatar : Array Expr) : MetaM (Option Expr) := do
  let some firstLiteral := first.regular[firstIndex]? | return none
  let some secondLiteral := second.regular[secondIndex]? | return none
  let positiveFirst ← Meta.withNewMCtxDepth do
    let some atom ← notArgument? secondLiteral | return none
    resolveOriented first second firstIndex secondIndex atom false targetRegular targetAvatar
  if positiveFirst.isSome then return positiveFirst
  Meta.withNewMCtxDepth do
    let some atom ← notArgument? firstLiteral | return none
    resolveOriented second first secondIndex firstIndex atom true targetRegular targetAvatar

/-- Generic binary resolution: substitutions are applied first and selected
literals are read at their reported indices. `Clause.resolve` performs exactly
the logical step; any literal-order change is a separate AC inference inserted
by parser-side preprocessing. The result remains in clause form. -/
private def listResolution (input : RuleInput) (info : ResolutionInfo) : MetaM (Option Expr) := do
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input info.substitutions targetBindings
      | return none
    let some first := instantiated[0]? | return none
    let some second := instantiated[1]? | return none
    let some firstIndex := info.resolvedLiterals[0]?.map (·.index) | return none
    let some secondIndex := info.resolvedLiterals[1]?.map (·.index) | return none
    let some firstClause ← resolutionClauseView first.1 first.2 | return none
    let some secondClause ← resolutionClauseView second.1 second.2 | return none
    let some targetLiterals := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) targetLiterals
    trace[vampire.replay] "resolution {input.step.name}: selected regular literals {firstIndex}/{secondIndex}; regular clauses contain {firstClause.regular.size}/{secondClause.regular.size} literals; AVATAR parts contain {firstClause.avatar.size}/{secondClause.avatar.size} literals"
    resolveViews firstClause secondClause firstIndex secondIndex targetRegular targetAvatar

/-- Reconstruction hook for Vampire's binary `resolution` inference.

The current certificate contract is deliberately strict about binary parents
and complete unifier/literal metadata. Literal indices may be arbitrary: the
clause-list view passes them directly to the position-aware clause theorem. -/
def resolution (input : RuleInput) (info : ResolutionInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 2 && input.parents.all (·.clauseForm) do
    return none
  unless info.substitutions.size == input.parents.size do
    return none
  unless info.resolvedLiterals.size == input.parents.size do
    return none
  unless (input.parents.zip info.resolvedLiterals).all fun (parent, literal) =>
    parent.parent.name == literal.parent do
    return none
  let substitutions := info.substitutions.map fun substitution =>
    let bindings := substitution.bindings.map fun (var, term) =>
      s!"{var} ↦ {MetadataTerm.toTptp term}"
    s!"{substitution.parent}[{String.intercalate ", " bindings.toList}]"
  trace[vampire.replay] "resolution {input.step.name}: {String.intercalate "; " substitutions.toList}"
  listResolution input info

/-- Reconstruct `forward_literal_rewriting`. Vampire matches the complement
of the selected side literal (second parent, a two-literal clause) onto the
rewritten literal of the first parent and puts the other side literal first.
That is binary resolution with the parents in the opposite order, so the
whole certificate is swapped and checked by `resolution`. -/
def forwardLiteralRewriting (input : RuleInput) (info : ResolutionInfo) :
    MetaM (Option Expr) := do
  unless input.parents.size == 2 do return none
  let some substitutions := orderParentSubstitutions input.parents info.substitutions
    | return none
  resolution { input with parents := input.parents.reverse }
    { substitutions := substitutions.reverse, resolvedLiterals := info.resolvedLiterals.reverse }

/-- Reconstruct `unit_resulting_resolution`. The first parent (the nucleus)
is resolved in turn against every unit parent, at the nucleus position the
certificate pairs with that unit. All substitutions are applied first, so
each intermediate step is ground binary resolution; the remaining nucleus
literals keep their order. -/
def unitResultingResolution (input : RuleInput) (info : ResolutionInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size ≥ 2 &&
      input.parents.all (·.clauseForm) do
    return none
  -- Positional: a unit clause may be used in several parent positions.
  unless info.substitutions.size == input.parents.size &&
      info.resolvedLiterals.size == 2 * (input.parents.size - 1) do
    return none
  let some nucleusParent := input.parents[0]? | return none
  let mut nucleusIndices := #[]
  for unit in [1:input.parents.size] do
    let some nucleusLiteral := info.resolvedLiterals[2 * (unit - 1)]? | return none
    let some unitLiteral := info.resolvedLiterals[2 * (unit - 1) + 1]? | return none
    let some unitParent := input.parents[unit]? | return none
    unless nucleusLiteral.parent == nucleusParent.parent.name &&
        unitLiteral.parent == unitParent.parent.name && unitLiteral.index == 0 do
      return none
    nucleusIndices := nucleusIndices.push nucleusLiteral.index
  unless nucleusIndices.toList.eraseDups.length == nucleusIndices.size do return none
  trace[vampire.replay] "unit-resulting resolution {input.step.name}: nucleus literals {nucleusIndices.toList} against {input.parents.size - 1} unit(s)"
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input info.substitutions targetBindings
      | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) target
    let some (nucleusProof, nucleusType) := instantiated[0]? | return none
    let some nucleus ← resolutionClauseView nucleusProof nucleusType | return none
    let mut current := nucleus
    -- Original nucleus positions of the literals still in `current`.
    let mut positions := Array.range nucleus.regular.size
    let mut result? := none
    for unit in [1:instantiated.size] do
      let some (unitProof, unitType) := instantiated[unit]? | return none
      let some unitView ← resolutionClauseView unitProof unitType | return none
      unless unitView.regular.size == 1 do return none
      let some index := positions.findIdx? (· == nucleusIndices[unit - 1]!) | return none
      let (stepRegular, stepAvatar) := if unit + 1 == instantiated.size then
        (targetRegular, targetAvatar)
      else
        (current.regular.eraseIdxIfInBounds index, current.avatar ++ unitView.avatar)
      -- The nucleus remainder comes first, as in Vampire's unit-resulting
      -- resolvent, whichever of the two selected literals is negative.
      let some proof ← resolveViews current unitView index 0 stepRegular stepAvatar
        | return none
      positions := positions.eraseIdxIfInBounds index
      result? := some proof
      if unit + 1 < instantiated.size then
        let some next ← resolutionClauseView proof (← inferType proof) | return none
        current := next
    pure result?

/-- A proof of `left = right` by congruence, where the two terms may differ
only at subterm pairs equated by an assumed constraint equation
`u = v` (used in either orientation). -/
private abbrev constrainedCongruence := congruenceWithEquations

/-- A proof of `source → target` for two atoms equal modulo the constraint
equations. An equation may also be selected in the other orientation. -/
private def constrainedImplication (equations : Array (Expr × Expr × Expr))
    (source target : Expr) : MetaM (Option Expr) := do
  if let some equality ← constrainedCongruence equations source target then
    return some (← withLocalDeclD `source source fun sourceProof => do
      mkLambdaFVars #[sourceProof] (← mkEqMP equality sourceProof))
  let some (_, sourceLeft, sourceRight) := (← whnfR source).eq? | return none
  let some (_, targetLeft, targetRight) := (← whnfR target).eq? | return none
  -- `sourceLeft = sourceRight` to `targetLeft = targetRight` via
  -- `targetLeft = sourceRight = sourceLeft = targetRight`.
  let some leftToRight ← constrainedCongruence equations sourceLeft targetRight | return none
  let some rightToLeft ← constrainedCongruence equations sourceRight targetLeft | return none
  withLocalDeclD `source source fun sourceProof => do
    let flipped ← mkEqTrans (← mkEqSymm rightToLeft)
      (← mkEqTrans (← mkEqSymm sourceProof) leftToRight)
    mkLambdaFVars #[sourceProof] flipped

/-- A proof of `¬ Holds constraints → first → second → False`, where every
constraint is a disequality `u ≠ v`. If no constraint holds, each `u = v`
holds, and the selected atoms are equal by congruence with these equations. -/
private def constrainedComplementary (constraints : Array Expr) (first second : Expr) :
    MetaM (Option Expr) := do
  let holds := mkApp (mkConst ``VampireHammer.Clause.Holds)
    (mkPropList constraints.toList)
  withLocalDeclD `noConstraint (mkNot holds) fun noConstraint =>
    withLocalDeclD `first first fun firstFVar =>
      withLocalDeclD `second second fun secondFVar => do
        let mut remaining := noConstraint
        let mut equations := #[]
        for index in [:constraints.size] do
          let constraint := constraints[index]!
          let some equation ← notArgument? constraint | return none
          let some (_, u, v) := (← whnfR equation).eq? | return none
          let rest := mkPropList (constraints.toList.drop (index + 1))
          let notConstraint ← mkAppM ``VampireHammer.Clause.notHeadOfNotHolds
            #[constraint, rest, remaining]
          let proof ← mkAppOptM ``Classical.byContradiction #[equation, notConstraint]
          equations := equations.push (proof, u, v)
          remaining ← mkAppM ``VampireHammer.Clause.notTailOfNotHolds #[constraint, rest, remaining]
        -- `first = A, second = ¬B` or `first = ¬A, second = B`.
        let contradiction? ← if let some negated ← notArgument? second then
            let some implication ← constrainedImplication equations first negated
              | pure none
            pure (some (mkApp secondFVar (mkApp implication firstFVar)))
          else if let some negated ← notArgument? first then
            let some implication ← constrainedImplication equations second negated
              | pure none
            pure (some (mkApp firstFVar (mkApp implication secondFVar)))
          else pure none
        let some contradiction := contradiction? | do
          trace[vampire.replay] "constrained resolution: {first} and {second} are not complementary modulo the constraints"
          return none
        unless ← isDefEq (← inferType contradiction) (mkConst ``False) do return none
        some <$> mkLambdaFVars #[noConstraint, firstFVar, secondFVar] contradiction

/-- Reconstruct `constrained_resolution` (resolution with unification with
abstraction). The selected literals agree only modulo the printed
constraints, which Vampire places first in the conclusion, followed by the
two parent tails. A-clause parents carry their AVATAR lists in parent order,
as in `AClause.resolve`. -/
def constrainedResolution (input : RuleInput) (info : ConstrainedResolutionInfo) :
    MetaM (Option Expr) := do
  let certificate := info.resolution
  unless input.sourceProof?.isNone && input.parents.size == 2 &&
      input.parents.all (·.clauseForm) do
    return none
  let some substitutions := orderParentSubstitutions input.parents certificate.substitutions
    | return none
  unless certificate.resolvedLiterals.size == 2 &&
      (input.parents.zip certificate.resolvedLiterals).all fun (parent, literal) =>
        parent.parent.name == literal.parent do
    return none
  let some firstIndex := certificate.resolvedLiterals[0]?.map (·.index) | return none
  let some secondIndex := certificate.resolvedLiterals[1]?.map (·.index) | return none
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input substitutions targetBindings
      | return none
    let some (firstProof, firstType) := instantiated[0]? | return none
    let some (secondProof, secondType) := instantiated[1]? | return none
    let some first ← resolutionClauseView firstProof firstType | return none
    let some second ← resolutionClauseView secondProof secondType | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) target
    unless targetRegular.size ≥ info.constraintCount do return none
    let constraints := targetRegular.take info.constraintCount
    let some firstLiteral := first.regular[firstIndex]? | return none
    let some secondLiteral := second.regular[secondIndex]? | return none
    let some complementary ← constrainedComplementary constraints firstLiteral secondLiteral
      | return none
    let list (literals : Array Expr) := mkPropList literals.toList
    let regularArguments := #[firstLiteral, secondLiteral, list constraints,
      list (first.regular.take firstIndex), list (first.regular.drop (firstIndex + 1)),
      list (second.regular.take secondIndex), list (second.regular.drop (secondIndex + 1))]
    let natural := constraints ++
      ((first.regular.eraseIdxIfInBounds firstIndex) ++ (second.regular.eraseIdxIfInBounds secondIndex))
    trace[vampire.replay] "constrained resolution {input.step.name}: selected literals {firstIndex}/{secondIndex} modulo {info.constraintCount} constraint(s); AVATAR parts contain {first.avatar.size}/{second.avatar.size} literals"
    if first.isAClause || second.isAClause then
      let asAClause (view : ResolutionClauseView) : MetaM Expr := do
        if view.isAClause then pure view.proof else
          mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[list view.regular, view.proof]
      let core := mkAppN (mkConst ``VampireHammer.Clause.AClause.constrainedResolve)
        (regularArguments ++ #[list first.avatar, list second.avatar, complementary,
          ← asAClause first, ← asAClause second])
      normalizeClauseResult core natural (first.avatar ++ second.avatar)
        targetRegular targetAvatar true
    else
      unless targetAvatar.isEmpty do return none
      let core := mkAppN (mkConst ``VampireHammer.Clause.constrainedResolve)
        (regularArguments ++ #[complementary, first.proof, second.proof])
      normalizeClauseResult core natural #[] targetRegular #[] false

/-- Orient unselected side literals so a forward-subsumption containment
certificate can use the main remainder literally.

Forward subsumption has set-like containment: each remaining side literal must
be a member of the main remainder.  Vampire may spell an equality in that side
remainder as `b = a` while the matching main literal is `a = b`.  The actual
`Contained` witness is deliberately definitionally strict, so bridge that
single side occurrence before building it.  We never change `excludedIndex`,
which is the literal selected for resolution and is handled separately by the
polarity check below.

The target occurrence is not consumed: `Clause.Contained` has set semantics,
so several side literals may validly use the same main literal. -/
private partial def orientRemainderForContainment (side : ResolutionClauseView)
    (excludedIndex : Nat) (mainRemainder : Array Expr) (index : Nat := 0) :
    MetaM (Option ResolutionClauseView) := do
  if index == side.regular.size then
    return some side
  if index == excludedIndex then
    return ← orientRemainderForContainment side excludedIndex mainRemainder (index + 1)
  let literal := side.regular[index]!
  -- Retain the compact original proof whenever the containment fact already
  -- holds definitionally.  The one-literal probe is discarded; the complete
  -- witness is constructed by the caller once every position is aligned.
  if (← containedWitness [literal] mainRemainder.toList).isSome then
    return ← orientRemainderForContainment side excludedIndex mainRemainder (index + 1)
  for mainLiteral in mainRemainder do
    -- A failed equality-orientation trial must not constrain metavariables
    -- used by the next possible match.
    let candidate ← Meta.withNewMCtxDepth do
      let some oriented ← orientRegularLiteralAt side index mainLiteral | return none
      orientRemainderForContainment oriented excludedIndex mainRemainder (index + 1)
    if candidate.isSome then
      return candidate
  pure none

/-- Apply forward subsumption resolution to two already instantiated clauses.

`mainIndex` and `sideIndex` are Vampire's two `resolved_literals` positions.
A candidate is accepted only when:

* its selected literal is the complement of the removed main literal;
* every other side literal occurs in the main remainder; and
* that main remainder has the decoded conclusion's occurrence order, allowing
  only pointwise equality orientation.

The containment check is what distinguishes this rule from ordinary
resolution.  Ordinary resolution would append the side remainder and can
therefore introduce duplicates; forward subsumption discards it because all
of its literals are already represented by the main remainder. -/
private def forwardSubsumptionClause (main side : ResolutionClauseView)
    (target : Array Expr) (mainIndex sideIndex : Nat) :
    MetaM (Option Expr) := do
  let some mainSelected := main.regular[mainIndex]? | return none
  let mainBefore := main.regular.take mainIndex
  let mainAfter := main.regular.drop (mainIndex + 1)
  let mainRemainder := mainBefore ++ mainAfter
  let some side ← orientRemainderForContainment side sideIndex mainRemainder
    | return none
  let some sideSelected := side.regular[sideIndex]? | return none
  let sideBefore := side.regular.take sideIndex
  let sideAfter := side.regular.drop (sideIndex + 1)
  let sideRemainder := sideBefore ++ sideAfter
  let some contained ← containedWitness sideRemainder.toList mainRemainder.toList
    | return none
  let mainBeforeList := mkPropList mainBefore.toList
  let mainAfterList := mkPropList mainAfter.toList
  let sideBeforeList := mkPropList sideBefore.toList
  let sideAfterList := mkPropList sideAfter.toList
  trace[vampire.replay] "forward subsumption: selected literals {mainIndex}/{sideIndex}; {sideRemainder.size} side remainder literal(s) contained in {mainRemainder.size} main literal(s)"
  let finish (core : Expr) : MetaM (Option Expr) :=
    normalizeClauseResult core mainRemainder #[] target #[] false

  -- First try `mainSelected = L` and `sideSelected = ¬L`.
  if let some sideAtom ← notArgument? sideSelected then
    if ← isDefEq mainSelected sideAtom then
      let core ← mkAppM ``VampireHammer.Clause.forwardSubsumptionResolveLiteral
        #[mainSelected, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, contained, main.proof, side.proof]
      return ← finish core
    -- The shared orientation API changes only the selected side occurrence,
    -- e.g. `¬(b = a)` to `¬(a = b)`, then provides a checked `Clause.map`
    -- proof for the opaque calculus theorem below.
    if let some orientedSide ← orientRegularLiteralAt side sideIndex
        (mkApp (mkConst ``Not) mainSelected) then
      let core ← mkAppM ``VampireHammer.Clause.forwardSubsumptionResolveLiteral
        #[mainSelected, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, contained, main.proof, orientedSide.proof]
      return ← finish core

  -- Then try `mainSelected = ¬L` and `sideSelected = L`.
  if let some mainAtom ← notArgument? mainSelected then
    if ← isDefEq mainAtom sideSelected then
      let core ← mkAppM ``VampireHammer.Clause.forwardSubsumptionResolveNegatedLiteral
        #[mainAtom, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, contained, main.proof, side.proof]
      return ← finish core
    if let some orientedSide ← orientRegularLiteralAt side sideIndex mainAtom then
      let core ← mkAppM ``VampireHammer.Clause.forwardSubsumptionResolveNegatedLiteral
        #[mainAtom, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, contained, main.proof, orientedSide.proof]
      return ← finish core
  pure none

/-- A-clause counterpart of `forwardSubsumptionClause`. Selection,
complementarity, and containment concern only the regular lists. The AVATAR
lists are checked against the conclusion and passed unchanged to the named
soundness lemma. -/
private def forwardSubsumptionAClause (main side : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr) (mainIndex sideIndex : Nat) :
    MetaM (Option Expr) := do
  let some mainSelected := main.regular[mainIndex]? | return none
  let mainBefore := main.regular.take mainIndex
  let mainAfter := main.regular.drop (mainIndex + 1)
  let mainRemainder := mainBefore ++ mainAfter
  let some side ← orientRemainderForContainment side sideIndex mainRemainder
    | return none
  let some sideSelected := side.regular[sideIndex]? | return none
  let sideBefore := side.regular.take sideIndex
  let sideAfter := side.regular.drop (sideIndex + 1)
  let sideRemainder := sideBefore ++ sideAfter
  let some contained ← containedWitness sideRemainder.toList mainRemainder.toList
    | return none
  let mainBeforeList := mkPropList mainBefore.toList
  let mainAfterList := mkPropList mainAfter.toList
  let sideBeforeList := mkPropList sideBefore.toList
  let sideAfterList := mkPropList sideAfter.toList
  let mainAvatarList := mkPropList main.avatar.toList
  let sideAvatarList := mkPropList side.avatar.toList
  let asAClause := fun (view : ResolutionClauseView) => do
    if view.isAClause then pure view.proof else
      let regularList := mkPropList view.regular.toList
      mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[regularList, view.proof]
  let mainProof ← asAClause main
  let sideProof ← asAClause side
  trace[vampire.replay] "forward subsumption A-clause: selected regular literals {mainIndex}/{sideIndex}; carrying {main.avatar.size}+{side.avatar.size} AVATAR literals"
  let finish (core : Expr) : MetaM (Option Expr) :=
    normalizeClauseResult core mainRemainder (main.avatar ++ side.avatar)
      targetRegular targetAvatar true
  if let some sideAtom ← notArgument? sideSelected then
    if ← isDefEq mainSelected sideAtom then
      let core ← mkAppM
        ``VampireHammer.Clause.AClause.forwardSubsumptionResolveLiteral
        #[mainSelected, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, mainAvatarList, sideAvatarList, contained,
          mainProof, sideProof]
      return ← finish core
    if let some orientedSide ← orientRegularLiteralAt side sideIndex
        (mkApp (mkConst ``Not) mainSelected) then
      let orientedProof ← asAClause orientedSide
      let core ← mkAppM
        ``VampireHammer.Clause.AClause.forwardSubsumptionResolveLiteral
        #[mainSelected, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, mainAvatarList, sideAvatarList, contained,
          mainProof, orientedProof]
      return ← finish core
  if let some mainAtom ← notArgument? mainSelected then
    if ← isDefEq mainAtom sideSelected then
      let core ← mkAppM
        ``VampireHammer.Clause.AClause.forwardSubsumptionResolveNegatedLiteral
        #[mainAtom, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, mainAvatarList, sideAvatarList, contained,
          mainProof, sideProof]
      return ← finish core
    if let some orientedSide ← orientRegularLiteralAt side sideIndex mainAtom then
      let orientedProof ← asAClause orientedSide
      let core ← mkAppM
        ``VampireHammer.Clause.AClause.forwardSubsumptionResolveNegatedLiteral
        #[mainAtom, mainBeforeList, mainAfterList, sideBeforeList,
          sideAfterList, mainAvatarList, sideAvatarList, contained,
          mainProof, orientedProof]
      return ← finish core
  pure none

/-- Replay `forward_subsumption_resolution` with an arbitrary side clause.

The first parent is the main clause and the second is the subsuming side
clause. Vampire reports only the literal deleted from the main clause and may
omit empty parent substitutions. After instantiation, each side occurrence is
considered in turn. The helpers below accept one only when it is complementary
to the removed literal and its remainder is contained in the main remainder. -/
def forwardSubsumptionResolution (input : RuleInput) (info : ForwardSubsumptionInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 2 && input.parents.all (·.clauseForm) do
    return none
  let some mainParentRef := input.parents[0]? | return none
  let some sideParentRef := input.parents[1]? | return none
  unless info.removedLiteral.parent == mainParentRef.parent.name do
    return none
  unless info.substitutions.all fun substitution =>
      input.parents.any fun parent => parent.parent.name == substitution.parent do
    return none
  -- The common instantiation helper expects one entry per parent in parent
  -- order. Vampire omits `subs(parent, [])`, so synthesize empty records.
  let substitutions := input.parents.map fun parent =>
    info.substitutions.find? (fun substitution => substitution.parent == parent.parent.name)
      |>.getD { parent := parent.parent.name, bindings := #[] }
  let mainSelection := info.removedLiteral
  trace[vampire.replay] "forward subsumption {input.step.name}: removed {mainSelection.parent}/{toString mainSelection.index}; searching the {sideParentRef.parent.name} side clause; {info.substitutions.size} explicit parent substitutions"
  underConclusionBinders input fun targetBindings _target => do
    let some instantiated ← instantiateParents input substitutions targetBindings
      | return none
    let some mainParent := instantiated[0]? | return none
    let some sideParent := instantiated[1]? | return none
    let some mainView ← resolutionClauseView mainParent.1 mainParent.2 | return none
    let some sideView ← resolutionClauseView sideParent.1 sideParent.2 | return none
    let some target := targetClauseLiterals? input targetBindings | return none
    for sideIndex in [:sideView.regular.size] do
      let candidate ← Meta.withNewMCtxDepth <| if mainView.isAClause || sideView.isAClause then
        let (targetRegular, targetAvatar) :=
          splitAClauseLiterals (avatarAtoms input) target
        forwardSubsumptionAClause mainView sideView targetRegular targetAvatar
          mainSelection.index sideIndex
      else
        forwardSubsumptionClause mainView sideView target mainSelection.index sideIndex
      if candidate.isSome then
        trace[vampire.replay] "forward subsumption {input.step.name}: inferred complementary side literal at regular index {sideIndex}"
        return candidate
    pure none

end VampireHammer.Backend

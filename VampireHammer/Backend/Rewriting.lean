import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation

/-!
Superposition and forward demodulation.

The two rules share occurrence rewriting and clause/A-clause transport. Vampire's
certificate identifies the rewritten parent and literal. The handler grounds
the parents first, rewrites all occurrences in the selected literal, and checks
the displayed conclusion through the shared orientation bridge.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Does `needle` occur syntactically in `haystack`?  Superposition uses this
small, deliberately strict test after the mgu has been materialized: a ground
rewrite must act on the literal occurrence that Vampire named.  The actual
proof below then checks the *whole* resulting clause definitionally, so this
test is only a useful early rejection and trace guard. -/
private def containsSyntacticOccurrence (needle haystack : Expr) : Bool :=
  haystack.find? (fun expression => expression == needle) |>.isSome

/-- Replace every syntactic occurrence using the same traversal that later
builds the congruence context. Keeping this operation shared ensures the
predicted natural clause and its proof cannot disagree about rewrite scope. -/
private def replaceSyntacticOccurrences (needle replacement expression : Expr) : Expr :=
  expression.replace fun candidate =>
    if candidate == needle then some replacement else none

/-- Build the congruence proof used by ground superposition.

For an equality `sourceTerm = targetTerm`, this constructs a function

```
sourceTerm = targetTerm → Clause.Holds source → Clause.Holds target
```

by making one proposition-valued context from the *complete* source clause.
`Expr.replace` visits every subexpression, so every syntactic occurrence of
`sourceTerm` in every literal is replaced at once.  The two `isDefEq` checks prevent
the certificate from silently accepting either a partial rewrite or a target
whose literal order differs from Vampire's displayed conclusion. -/
private def rewriteAllOccurrences (sourceHolds targetHolds equation sourceTerm targetTerm : Expr)
    (reverseEquality : Bool) :
    MetaM (Option Expr) := do
  withLocalDeclD `superpositionEquality equation fun equalityProof => do
    withLocalDeclD `superpositionSource sourceHolds fun sourceProof => do
      let sourceTermType ← inferType sourceTerm
      withLocalDeclD `superpositionHole sourceTermType fun hole => do
        let contextBody := replaceSyntacticOccurrences sourceTerm hole sourceHolds
        -- If no replacement happened, an equality proof would merely prove
        -- `Holds source = Holds source`.  That is not a superposition step.
        unless containsSyntacticOccurrence hole contextBody do return none
        let context ← mkLambdaFVars #[hole] contextBody
        unless ← isDefEq (mkApp context sourceTerm) sourceHolds do return none
        unless ← isDefEq (mkApp context targetTerm) targetHolds do return none
        -- Vampire can use either orientation of the positive equality.  The
        -- theorem still receives its displayed proof `equation`; only this
        -- local congruence application needs `Eq.symm` for right-to-left.
        let directionalEquality ← if reverseEquality then mkEqSymm equalityProof
          else pure equalityProof
        let clauseEquality ← mkCongrArg context directionalEquality
        let targetProof ← mkEqMP clauseEquality sourceProof
        let bySource ← mkLambdaFVars #[sourceProof] targetProof
        some <$> mkLambdaFVars #[equalityProof] bySource

/-- Build the congruence proof for forward demodulation of one named clause
literal.  Vampire's `rewritten_literal` certificate selects the literal in
which every matching term occurrence is replaced; equal terms in other
literals remain untouched. -/
private def rewriteLiteralOccurrences (source target : Array Expr) (sourceIndex : Nat)
    (equation sourceTerm targetTerm : Expr) (reverseEquality : Bool) :
    MetaM (Option Expr) := do
  let some sourceLiteral := source[sourceIndex]? | return none
  unless source.size == target.size do return none
  let sourceHolds ← holdsType source
  let targetHolds ← holdsType target
  withLocalDeclD `demodulationEquality equation fun equalityProof => do
    withLocalDeclD `demodulationSource sourceHolds fun sourceProof => do
      let sourceTermType ← inferType sourceTerm
      withLocalDeclD `demodulationHole sourceTermType fun hole => do
        let contextLiteral := replaceSyntacticOccurrences sourceTerm hole sourceLiteral
        unless containsSyntacticOccurrence hole contextLiteral do return none
        let contextBody ← holdsType (source.set! sourceIndex contextLiteral)
        let context ← mkLambdaFVars #[hole] contextBody
        unless ← isDefEq (mkApp context sourceTerm) sourceHolds do return none
        unless ← isDefEq (mkApp context targetTerm) targetHolds do return none
        let directionalEquality ← if reverseEquality then mkEqSymm equalityProof
          else pure equalityProof
        let clauseEquality ← mkCongrArg context directionalEquality
        let targetProof ← mkEqMP clauseEquality sourceProof
        let bySource ← mkLambdaFVars #[sourceProof] targetProof
        some <$> mkLambdaFVars #[equalityProof] bySource

/-- Apply ground superposition to two instantiated parent clauses.

The selected rewritten literal comes from Vampire's annotation. Vampire does
not separately report the equality occurrence or its direction, so this
function searches the other parent for a positive equality and accepts the
a candidate whose all-occurrences rewrite and unused tail exactly match
the displayed conclusion. The natural theorem order is retained: rewritten
source literals first, followed by the equality parent's remaining literals. -/
private def superposeClauses (rewrittenProof equalityProof : Expr)
    (rewritten equality target : Array Expr) (rewrittenIndex : Nat) :
    MetaM (Option Expr) := do
  let some selectedLiteral := rewritten[rewrittenIndex]? | return none
  if equality.isEmpty || target.size + 1 != rewritten.size + equality.size then
    return none
  let sourceHolds ← holdsType rewritten
  let sourceList := mkPropList rewritten.toList
  for equalityIndex in [:equality.size] do
    let equation ← whnf equality[equalityIndex]!
    let some (_, left, right) := equation.eq? | continue
    let equalityBefore := equality.take equalityIndex
    let equalityAfter := equality.drop (equalityIndex + 1)
    let equalityRemainder := equalityBefore ++ equalityAfter
    let equalityBeforeList := mkPropList equalityBefore.toList
    let equalityAfterList := mkPropList equalityAfter.toList
    let tryOrientation (sourceTerm targetTerm : Expr) (reverseEquality : Bool) :
        MetaM (Option Expr) := do
      unless containsSyntacticOccurrence sourceTerm selectedLiteral do return none
      let naturalTarget := rewritten.map
        (replaceSyntacticOccurrences sourceTerm targetTerm)
      let naturalTargetHolds ← holdsType naturalTarget
      let naturalTargetList := mkPropList naturalTarget.toList
      let some rewrite ← rewriteAllOccurrences sourceHolds naturalTargetHolds equation
        sourceTerm targetTerm reverseEquality | return none
      let core ← mkAppM ``VampireHammer.Clause.superpose
        #[equation, sourceList, naturalTargetList, equalityBeforeList,
          equalityAfterList, rewrite, rewrittenProof, equalityProof]
      -- The rewrite fixes literal order. Vampire may nevertheless print a
      -- resulting equality in the symmetric orientation, so normalize only
      -- pointwise equality orientations here; no clause permutation is hidden.
      normalizeRegularEqualityResult core (naturalTarget ++ equalityRemainder) target
    -- The first direction is conventional left-to-right. Separate metavariable
    -- depths ensure a failed orientation cannot constrain the next attempt.
    let forward ← Meta.withNewMCtxDepth <| tryOrientation left right false
    if let some proof := forward then
      trace[vampire.replay] "superposition: selected equality literal {equalityIndex}, left-to-right"
      return some proof
    let reverse ← Meta.withNewMCtxDepth <| tryOrientation right left true
    if let some proof := reverse then
      trace[vampire.replay] "superposition: selected equality literal {equalityIndex}, right-to-left"
      return some proof
  trace[vampire.replay] "superposition candidate mismatch: rewritten literals {rewritten}; equality literals {equality}; displayed target {target}"
  pure none

/-- Superpose the regular halves of A-clauses and retain their AVATAR context.

`ResolutionClauseView` gives ordinary clauses an empty AVATAR half, so this
also covers a mixed inference such as an A-clause rewritten by an ordinary
unit equality.  The selected literal index refers only to `rewritten.regular`;
Vampire's AVATAR literals are not first-order literals and must never be
searched or rewritten here.

The ordinary `Clause.superpose` theorem is used internally by the named
`AClause.superpose` bridge.  If the resulting regular list needs equality
orientation normalization, `AClause.mapFirstOrder` performs that local bridge
without touching the carried AVATAR list. -/
private def superposeAClauses (rewritten equality : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr) (rewrittenIndex : Nat) :
    MetaM (Option Expr) := do
  let some selectedLiteral := rewritten.regular[rewrittenIndex]? | return none
  if equality.regular.isEmpty ||
      targetRegular.size + 1 != rewritten.regular.size + equality.regular.size then
    return none
  let sourceHolds ← holdsType rewritten.regular
  let sourceList := mkPropList rewritten.regular.toList
  let equalityList := mkPropList equality.regular.toList
  let sourceAvatarList := mkPropList rewritten.avatar.toList
  let equalityAvatarList := mkPropList equality.avatar.toList
  -- `AClause.superpose` deliberately has one uniform type for both parents.
  -- Lift any ordinary parent through the named empty-AVATAR embedding instead
  -- of relying on definitional unfolding of the two representations.
  let rewrittenProof ← if rewritten.isAClause then pure rewritten.proof else
    mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[sourceList, rewritten.proof]
  let equalityProof ← if equality.isAClause then pure equality.proof else
    mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[equalityList, equality.proof]
  for equalityIndex in [:equality.regular.size] do
    let equation ← whnf equality.regular[equalityIndex]!
    let some (_, left, right) := equation.eq? | continue
    let equalityBefore := equality.regular.take equalityIndex
    let equalityAfter := equality.regular.drop (equalityIndex + 1)
    let equalityRemainder := equalityBefore ++ equalityAfter
    let equalityBeforeList := mkPropList equalityBefore.toList
    let equalityAfterList := mkPropList equalityAfter.toList
    let tryOrientation (sourceTerm targetTerm : Expr) (reverseEquality : Bool) :
        MetaM (Option Expr) := do
      unless containsSyntacticOccurrence sourceTerm selectedLiteral do return none
      let naturalTarget := rewritten.regular.map
        (replaceSyntacticOccurrences sourceTerm targetTerm)
      let naturalResult := naturalTarget ++ equalityRemainder
      let naturalTargetHolds ← holdsType naturalTarget
      let naturalTargetList := mkPropList naturalTarget.toList
      let some rewrite ← rewriteAllOccurrences sourceHolds naturalTargetHolds equation
        sourceTerm targetTerm reverseEquality | return none
      let core ← mkAppM ``VampireHammer.Clause.AClause.superpose
        #[equation, sourceList, naturalTargetList, equalityBeforeList, equalityAfterList,
          sourceAvatarList, equalityAvatarList, rewrite, rewrittenProof, equalityProof]
      -- The common result adapter is also responsible for the rare case in
      -- which an untouched equality remainder is printed symmetrically.
      normalizeClauseResult core naturalResult (rewritten.avatar ++ equality.avatar)
        targetRegular targetAvatar true
    let forward ← Meta.withNewMCtxDepth <| tryOrientation left right false
    if let some proof := forward then
      trace[vampire.replay] "superposition: selected equality literal {equalityIndex}, left-to-right (A-clause)"
      return some proof
    let reverse ← Meta.withNewMCtxDepth <| tryOrientation right left true
    if let some proof := reverse then
      trace[vampire.replay] "superposition: selected equality literal {equalityIndex}, right-to-left (A-clause)"
      return some proof
  pure none

/-- Choose ordinary or A-clause superposition after both parents have been
instantiated.  The latter is necessary whenever either parent carries AVATAR
literals, even if the other parent is an ordinary unit equality. -/
private def superposeClauseViews (rewritten equality : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr) (rewrittenIndex : Nat) :
    MetaM (Option Expr) :=
  if rewritten.isAClause || equality.isAClause then
    superposeAClauses rewritten equality targetRegular targetAvatar rewrittenIndex
  else
    if !targetAvatar.isEmpty then
      pure none
    else
      superposeClauses rewritten.proof equality.proof rewritten.regular equality.regular
        targetRegular rewrittenIndex

/-- Reconstruct ground `superposition`. The mgu is first applied exactly as
for resolution; then `superposeClauses` finds the positive equality occurrence,
rewrites every matching term occurrence in the named parent clause, and carries
the equality parent's remaining literals into the conclusion. -/
def superposition (input : RuleInput) (info : SuperpositionInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 2 && input.parents.all (·.clauseForm) do
    trace[vampire.replay] "superposition {input.step.name} declined: expected two clause-form parents"
    return none
  unless info.substitutions.size == input.parents.size do
    trace[vampire.replay] "superposition {input.step.name} declined: expected one substitution for each parent, got {info.substitutions.size}"
    return none
  -- Vampire orders these records by their role in the inference (rewritten
  -- parent first), which need not be the order of the proof-parent array.
  -- Pair them by the explicit parent name before using the common positional
  -- instantiation helper.
  let some substitutions := orderParentSubstitutions input.parents info.substitutions | do
    trace[vampire.replay] "superposition {input.step.name} declined: no substitution for a named parent occurrence"
    return none
  let some rewrittenParentIndex := input.parents.findIdx?
    (fun parent => parent.parent.name == info.rewrittenLiteral.parent) | do
      trace[vampire.replay] "superposition {input.step.name} declined: rewritten-literal parent `{info.rewrittenLiteral.parent}` is absent"
      return none
  let equalityParentIndex := if rewrittenParentIndex == 0 then 1 else 0
  let result ← underConclusionBinders input fun targetBindings _target => do
    trace[vampire.replay] "superposition {input.step.name}: opened {targetBindings.size} conclusion binder(s)"
    -- Superposition uses the same shared erased-variable environment as all
    -- other calculus rules.  In particular, this also handles an equality
    -- substitution that refers to a variable erased from the rewritten
    -- parent, independently of the order in which Vampire printed parents.
    let some instantiated ← instantiateParents input substitutions targetBindings
      | do
        trace[vampire.replay] "superposition {input.step.name} declined: could not instantiate parent substitutions"
        return none
    let some rewrittenParent := instantiated[rewrittenParentIndex]? | do
      trace[vampire.replay] "superposition {input.step.name} declined: rewritten parent index is invalid"
      return none
    let some equalityParent := instantiated[equalityParentIndex]? | do
      trace[vampire.replay] "superposition {input.step.name} declined: equality parent index is invalid"
      return none
    let some rewrittenClause ← resolutionClauseView rewrittenParent.1 rewrittenParent.2
      | do
        trace[vampire.replay] "superposition {input.step.name} declined: rewritten parent is not a clause"
        return none
    let some equalityClause ← resolutionClauseView equalityParent.1 equalityParent.2
      | do
        trace[vampire.replay] "superposition {input.step.name} declined: equality parent is not a clause"
        return none
    let some targetLiterals := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) targetLiterals
    trace[vampire.replay] "superposition {input.step.name}: rewrite all occurrences in {info.rewrittenLiteral.parent}/{info.rewrittenLiteral.index}; regular literals {rewrittenClause.regular.size}/{equalityClause.regular.size}/{targetRegular.size}; AVATAR literals {rewrittenClause.avatar.size}/{equalityClause.avatar.size}/{targetAvatar.size}"
    superposeClauseViews rewrittenClause equalityClause targetRegular targetAvatar
      info.rewrittenLiteral.index
  if result.isNone then
    trace[vampire.replay] "superposition {input.step.name} declined: the instantiated all-occurrences rewrite did not match the displayed clause"
  pure result

/-- Apply one instantiated unit equality as a demodulation rule to every
matching occurrence in the certificate-selected literal.  As with
superposition, both equality directions are tried, but the complete natural
result must match the decoded target position by position, allowing only
equality symmetry. -/
private def demodulateClauses (rewrittenProof equalityProof : Expr)
    (rewritten equality target : Array Expr) (rewrittenIndex : Nat) : MetaM (Option Expr) := do
  unless equality.size == 1 && target.size == rewritten.size do return none
  let some selectedLiteral := rewritten[rewrittenIndex]? | return none
  let equation ← whnf equality[0]!
  let some (_, left, right) := equation.eq? | return none
  let sourceList := mkPropList rewritten.toList
  let tryOrientation (sourceTerm targetTerm : Expr) (reverseEquality : Bool) :
      MetaM (Option Expr) := do
    unless containsSyntacticOccurrence sourceTerm selectedLiteral do return none
    let rewrittenLiteral := replaceSyntacticOccurrences sourceTerm targetTerm selectedLiteral
    let naturalTarget := rewritten.set! rewrittenIndex rewrittenLiteral
    let naturalTargetList := mkPropList naturalTarget.toList
    let some rewrite ← rewriteLiteralOccurrences rewritten naturalTarget rewrittenIndex
      equation sourceTerm targetTerm reverseEquality | return none
    let core ← mkAppM ``VampireHammer.Clause.demodulate
      #[equation, sourceList, naturalTargetList, rewrite, rewrittenProof, equalityProof]
    normalizeRegularEqualityResult core naturalTarget target
  let forward ← Meta.withNewMCtxDepth <| tryOrientation left right false
  if let some proof := forward then
    trace[vampire.replay] "forward demodulation: rewrote left-to-right"
    return some proof
  let reverse ← Meta.withNewMCtxDepth <| tryOrientation right left true
  if let some proof := reverse then
    trace[vampire.replay] "forward demodulation: rewrote right-to-left"
    return some proof
  pure none

/-- Forward-demodulate regular A-clause halves, preserving their AVATAR parts.

This is the unit-equality counterpart of `superposeAClauses`. The equality
literal is consumed rather than retained, while both AVATAR halves remain
alternatives in the child. Equality-orientation normalization is lifted over
the regular half with `AClause.mapFirstOrder`. -/
private def demodulateAClauses (rewritten equality : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr) (rewrittenIndex : Nat) : MetaM (Option Expr) := do
  unless equality.regular.size == 1 && targetRegular.size == rewritten.regular.size do
    return none
  let some selectedLiteral := rewritten.regular[rewrittenIndex]? | return none
  let equation ← whnf equality.regular[0]!
  let some (_, left, right) := equation.eq? | return none
  let sourceList := mkPropList rewritten.regular.toList
  let equalityList := mkPropList equality.regular.toList
  let sourceAvatarList := mkPropList rewritten.avatar.toList
  let equalityAvatarList := mkPropList equality.avatar.toList
  let rewrittenProof ← if rewritten.isAClause then pure rewritten.proof else
    mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[sourceList, rewritten.proof]
  let equalityProof ← if equality.isAClause then pure equality.proof else
    mkAppM ``VampireHammer.Clause.AClause.ofFirstOrder #[equalityList, equality.proof]
  let tryOrientation (sourceTerm targetTerm : Expr) (reverseEquality : Bool) :
      MetaM (Option Expr) := do
    unless containsSyntacticOccurrence sourceTerm selectedLiteral do return none
    let rewrittenLiteral := replaceSyntacticOccurrences sourceTerm targetTerm selectedLiteral
    let naturalTarget := rewritten.regular.set! rewrittenIndex rewrittenLiteral
    let naturalTargetList := mkPropList naturalTarget.toList
    let some rewrite ← rewriteLiteralOccurrences rewritten.regular naturalTarget rewrittenIndex
      equation sourceTerm targetTerm reverseEquality | return none
    let core ← mkAppM ``VampireHammer.Clause.AClause.demodulate
      #[equation, sourceList, naturalTargetList, sourceAvatarList, equalityAvatarList,
        rewrite, rewrittenProof, equalityProof]
    normalizeClauseResult core naturalTarget (rewritten.avatar ++ equality.avatar)
      targetRegular targetAvatar true
  let forward ← Meta.withNewMCtxDepth <| tryOrientation left right false
  if let some proof := forward then
    trace[vampire.replay] "forward demodulation: rewrote left-to-right (A-clause)"
    return some proof
  let reverse ← Meta.withNewMCtxDepth <| tryOrientation right left true
  if let some proof := reverse then
    trace[vampire.replay] "forward demodulation: rewrote right-to-left (A-clause)"
    return some proof
  pure none

/-- Choose ordinary or A-clause forward demodulation after instantiation. -/
private def demodulateClauseViews (rewritten equality : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr) (rewrittenIndex : Nat) : MetaM (Option Expr) :=
  if rewritten.isAClause || equality.isAClause then
    demodulateAClauses rewritten equality targetRegular targetAvatar rewrittenIndex
  else
    if !targetAvatar.isEmpty then pure none else
      demodulateClauses rewritten.proof equality.proof rewritten.regular equality.regular targetRegular
        rewrittenIndex

/-- Reconstruct Vampire's ground `forward_demodulation` inference.

`rewritten_literal` selects the parent and the literal being simplified; the
other parent is a unit positive equality. The certificate contains one
parent-local substitution for each parent, including an explicit empty
substitution for an unchanged rewritten parent. After applying both
substitutions, the handler checks the selected literal position, rewrites
every matching occurrence in that literal, and validates the complete
displayed conclusion. -/
def forwardDemodulation (input : RuleInput) (info : ForwardDemodulationInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 2 &&
      input.parents.all (·.clauseForm) &&
      info.substitutions.size == input.parents.size do
    return none
  -- Parent names, rather than their array position, are the authority here.
  -- `orderParentSubstitutions` additionally handles a legal self-inference,
  -- where the same proof node occurs twice with two different substitutions.
  let some substitutions := orderParentSubstitutions input.parents info.substitutions
    | return none
  let some rewrittenParentIndex := input.parents.findIdx?
    (fun parent => parent.parent.name == info.rewrittenLiteral.parent)
    | do
      trace[vampire.replay] "forward demodulation {input.step.name} declined: rewritten-literal parent `{info.rewrittenLiteral.parent}` is absent"
      return none
  let equalityParentIndex := if rewrittenParentIndex == 0 then 1 else 0
  underConclusionBinders input fun targetBindings _target => do
    -- Reuse the ordinary calculus instantiator.  It pre-allocates variables
    -- which disappear in a redex before materializing either parent, so the
    -- equality substitution may freely mention such a variable.
    let some instantiated ← instantiateParents input substitutions targetBindings
      | return none
    let some rewrittenParent := instantiated[rewrittenParentIndex]? | return none
    let some equalityParent := instantiated[equalityParentIndex]? | return none
    let some rewrittenView ← resolutionClauseView rewrittenParent.1 rewrittenParent.2
      | return none
    let some equalityView ← resolutionClauseView equalityParent.1 equalityParent.2
      | return none
    let some targetLiterals := targetClauseLiterals? input targetBindings | return none
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) targetLiterals
    -- The reference indexes the flattened first-order clause spelling. The
    -- selected literal must therefore be in the regular part, never in the
    -- carried AVATAR context. The rewrite changes every matching occurrence
    -- inside this named literal and leaves all other literals unchanged.
    unless info.rewrittenLiteral.index < rewrittenView.regular.size do
      trace[vampire.replay] "forward demodulation {input.step.name} declined: rewritten literal index {info.rewrittenLiteral.index} is outside regular parent {info.rewrittenLiteral.parent}"
      return none
    unless equalityView.regular.size == 1 do
      trace[vampire.replay] "forward demodulation {input.step.name} declined: equality parent is not a unit regular clause"
      return none
    let selectedLiteral := rewrittenView.regular[info.rewrittenLiteral.index]!
    let equation ← whnf equalityView.regular[0]!
    let some (_, left, right) := equation.eq? | do
      trace[vampire.replay] "forward demodulation {input.step.name} declined: equality parent does not contain an equality literal"
      return none
    unless containsSyntacticOccurrence left selectedLiteral ||
        containsSyntacticOccurrence right selectedLiteral do
      trace[vampire.replay] "forward demodulation {input.step.name} declined: selected literal {info.rewrittenLiteral.parent}/{info.rewrittenLiteral.index} contains neither side of the instantiated equality"
      return none
    trace[vampire.replay] "forward demodulation {input.step.name}: rewrite all occurrences in {info.rewrittenLiteral.parent}/{info.rewrittenLiteral.index}; regular literals {rewrittenView.regular.size}/{equalityView.regular.size}/{targetRegular.size}; AVATAR literals {rewrittenView.avatar.size}/{equalityView.avatar.size}/{targetAvatar.size}"
    trace[vampire.replay] "forward demodulation {input.step.name}: instantiated rewritten literals {rewrittenView.regular}; equality literals {equalityView.regular}; target literals {targetRegular}"
    Meta.withNewMCtxDepth <| demodulateClauseViews rewrittenView equalityView
      targetRegular targetAvatar info.rewrittenLiteral.index

end VampireHammer.Backend

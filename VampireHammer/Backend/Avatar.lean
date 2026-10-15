import VampireHammer.Backend.Metadata
import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation
import VampireHammer.Backend.AvatarPrenex
import VampireHammer.Backend_Preprocessing

/-!
AVATAR component, split, and contradiction inferences.

Split reconstruction first transports the AVATAR context, then expands the
certified definitions. Binder recovery uses Vampire's split annotation when
available. Regular literals retain their ordered clause representation;
AVATAR transport is distinct from ordinary calculus inference reconstruction.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Instantiate the leading universal binders of a proposition *as a type*.

Unlike a proof of `∀ x, P x`, the proposition `∀ x, P x` is not a function
term and therefore cannot be passed to `mkApp`.  Its body must be opened with
`instantiate1`. This helper keeps that distinction explicit and checks every
domain while the AVATAR component handler aligns a definition's binder prefix
with the child clause prefix. -/
private def instantiateForallFormula (formula : Expr) (values : Array Expr) : MetaM (Option Expr) := do
  let mut formula := formula
  for value in values do
    formula ← whnf formula
    unless formula.isForall do return none
    unless ← isDefEq formula.bindingDomain! (← inferType value) do return none
    formula := formula.bindingBody!.instantiate1 value
  pure (some formula)

/-- Reconstruct `avatar_component_clause` directly from its definition node.

The definition parent is the singleton clause `[split ↔ component]`. Its
child states `component ∨ ¬split`.  A component can itself have leading
universal binders, in which case Vampire prints the child as
`∀ x₁ … xₙ, componentBody x₁ … xₙ ∨ ¬split`.  The older clause theorem is
ideal for the unquantified case, but cannot move those binders.  Instead this
handler opens exactly the child binders, assumes `split`, obtains the complete
component with `Iff.mp` (or `Iff.mpr` for a symmetric definition), and applies
it to the opened variables.  The other branch is simply `¬split`.

The definition's component can use another grouping or literal order than
its displayed component clause. A checked `Clause.reorder` transports the
identical literal occurrences at this definition boundary, including the
negative split literal; this also covers `¬split ∨ component`.

All resulting terms are checked against the displayed parser target. No proof
search is used, so quantified AVATAR components do not depend on `grind`'s
E-matching behavior. -/
def avatarComponentClause (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  unless parent.binders.isEmpty do return none
  -- The parent is stored in `Clause.Holds` after CNF. Recover just its
  -- original singleton formula before using `Iff.mp`; this is a local rule
  -- boundary and does not change the proof-DAG representation.
  let some definitionProof ← fromClauseForm parent.proof parent.target 0 parent.clauseLiterals?
    | return none
  let definitionType ← whnf (← inferType definitionProof)
  let (.app (.app (.const ``Iff _) left) right) := definitionType | return none
  let atoms := avatarAtoms input
  let (split, component, splitOnLeft) ←
    if atoms.any (· == left) then pure (left, right, true)
    else if atoms.any (· == right) then pure (right, left, false)
    else return none
  -- `Lam2D` commonly represents `∀ x, P x` as an application of its
  -- polymorphic forall encoding.  Reduce that application before attaching
  -- the target binder values; `mkAppN` itself is purely syntactic and cannot
  -- apply through this beta-redex.
  let component ← whnf component
  underConclusionBinders input fun targetBindings targetBody => do
    let values := targetBindings.map (·.2)
    -- Instantiating the component proposition opens its Pi type. Applying a
    -- *proof* of that proposition below is a separate operation and does use
    -- `mkAppN` with these same checked values.
    let some componentInstance ← instantiateForallFormula component values
      | return none
    let componentType ← inferType componentInstance
    unless ← isDefEq componentType (mkSort Level.zero) do return none
    let negativeSplit := mkApp (mkConst ``Not) split
    let canonicalType := mkAppN (mkConst ``Or) #[componentInstance, negativeSplit]

    let positiveBranch? ← withLocalDeclD `avatarComponentPositive split fun positive => do
      let universalComponent ← if splitOnLeft then
        mkAppM ``Iff.mp #[definitionProof, positive]
      else
        mkAppM ``Iff.mpr #[definitionProof, positive]
      let componentProof := mkAppN universalComponent values
      let result ← mkAppOptM ``Or.inl
        #[some componentInstance, some negativeSplit, some componentProof]
      if ← isDefEq (← inferType result) canonicalType then
        some <$> mkLambdaFVars #[positive] result
      else
        pure none
    let some positiveBranch := positiveBranch? | return none

    let negativeBranch? ← withLocalDeclD `avatarComponentNegative negativeSplit fun negative => do
      let result ← mkAppOptM ``Or.inr
        #[some componentInstance, some negativeSplit, some negative]
      if ← isDefEq (← inferType result) canonicalType then
        some <$> mkLambdaFVars #[negative] result
      else
        pure none
    let some negativeBranch := negativeBranch? | return none

    let cases ← mkAppM ``Classical.em #[split]
    let canonical ← mkAppM ``Or.elim #[cases, positiveBranch, negativeBranch]
    if let some result ← asExpectedType canonical targetBody then
      return some result
    -- The definition's component and its clause can use different `Or`
    -- grouping, and Vampire sorts the literals in the displayed definition.
    -- Compare their concrete occurrence lists, with the naming predicates
    -- still folded, and expose any required permutation as `Clause.reorder`.
    -- This is the definition-to-clause boundary; calculus handlers retain
    -- their stricter requirement that reordered conclusions cite an AC step.
    let sourceTree ← clauseTree canonicalType
    let sourceClause ← mkAppM ``VampireHammer.Clause.Tree.toHolds #[sourceTree, canonical]
    let sourceLiterals ← flattenClause canonicalType
    let targetLiterals ← flattenClause targetBody
    let some aligned ← reorderAndNormalize sourceClause sourceLiterals.toList
      targetLiterals.toList | return none
    let targetTree ← clauseTree targetBody
    let result ← mkAppM ``VampireHammer.Clause.Tree.fromHolds #[targetTree, aligned]
    asExpectedType result targetBody

/-- Reconstruct `avatar_contradiction_clause`. `$false` was removed from the
literal array by `decodeClausePhase`, so the regular part of an A-clause is
empty on both sides. Its AVATAR literals are transported as a set; an ordinary
clause still uses the legacy list-clause identity below. -/
def avatarContradictionClause (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.step.binders.isEmpty do return none
  let some parent := input.parents[0]? | return none
  let some target := input.clauseLiterals? | return none
  if let some source ← aClauseView parent.proof (← inferType parent.proof) then
    let (targetRegular, targetAvatar) :=
      splitAClauseLiterals (avatarAtoms input) target
    unless source.regular.isEmpty && targetRegular.isEmpty do return none
    let sourceAvatarList := mkPropList source.avatar.toList
    let core ← mkAppM ``VampireHammer.Clause.AClause.avatarContradictionClause
      #[sourceAvatarList, source.proof]
    return ← transportAvatarSet core #[] source.avatar targetAvatar
  let some (_, source) ← clauseView parent.proof (← inferType parent.proof)
    | return none
  let sourceList := mkPropList source.toList
  let proof ← mkAppM ``VampireHammer.Clause.avatarContradictionClause
    #[sourceList, parent.proof]
  reorderAndNormalize proof source.toList target.toList

/- Reconstruct the first-order-to-propositional boundary represented by
`avatar_split_clause`.

Vampire cites one A-clause together with the definitions of the split symbols
that summarize parts of its regular clause. We first match literal occurrences
already present on the parent's AVATAR side. They are carried into the child
unchanged. A definition is rewritten only for a remaining split literal,
with either polarity: `s ↔ P` changes `s` to `P` and `¬s` to `¬P`. After
expansion, VampLean's `prenexify` moves independent universal quantifiers to
the outer position used by the parent clause. The local proof then uses the
same `ac_nf0`/`ac_nf` normalization as the paper-style proof scripts to align
the regular clause before applying its principal parent. The source-ordered
result is then transported to Vampire's displayed AVATAR context by
`AClause.transportAvatarSet`.

Keeping this as a separate handler matters because unfolding carried AVATAR
conditions can turn a small propositional goal back into a large first-order
one. The handler rewrites only definitions of newly introduced split atoms. -/

/-- Close an expanded AVATAR split using the AC normalizer used by the
paper-style proof format.

After the selected definitions are rewritten into the goal, the source clause
and expanded target may group their literals differently and may introduce
their universal binders in different orders. `prenexify` exposes the same
universal prefix; `ac_nf0` canonicalizes the source hypothesis and `ac_nf`
canonicalizes the goal. Equality and disequality are first put into one
orientation using their two explicit symmetry laws. This produces a compact
local proof and delegates the standard associative/commutative normalization
to VampLean instead of trying to infer a variable permutation in the backend. -/
private def closeAvatarGoalByAC (goal : MVarId) (source : Expr) : MetaM Bool := do
  let sourceDecl ← getFVarLocalDecl source
  let src := mkIdent sourceDecl.userName
  -- Equality orientation is handled structurally by VampLean's `symm_match`
  -- rather than by `simp only [eq_comm, ne_comm]`: that permutation simp
  -- orders terms with `acLt`, which reduces its arguments and can unfold a
  -- Skolem function's `Classical.choose` value.  The direct attempt covers
  -- splits whose literal order is unchanged; otherwise `ac_nf` first
  -- normalizes the order of both sides.
  let direct ← `(tactic|
    (prenexify at $src:ident
     intros))
  let normalized ← `(tactic|
    (prenexify at $src:ident
     ac_nf0 at $src:ident
     intros
     ac_nf))
  for tactic in [direct, normalized] do
    let saved ← saveState
    try
      let (remaining, _) ← Lean.Elab.runTactic goal tactic
      if remaining.isEmpty then return true
      if let [remainingGoal] := remaining then
        -- Call the implementation behind `symm_match` directly. A failed
        -- speculative match then raises a recoverable Meta error without
        -- leaving an error diagnostic in the enclosing source file.
        remainingGoal.withContext do
          -- `prenexify` and `ac_nf0 at h` may replace `h` with a new local
          -- declaration. Resolve it again by its stable user name instead of
          -- retaining the now-invalid fvar from the original goal context.
          let currentSource := (← getLocalDeclFromUserName sourceDecl.userName).toExpr
          let sourceType ← inferType currentSource
          let targetType ← remainingGoal.getType
          let equality ← VampLean.symmUnify sourceType targetType
          let proof ← mkAppM ``Eq.mp #[equality, currentSource]
          remainingGoal.assign proof
        return true
    catch error =>
      trace[vampire.replay] "AVATAR split AC attempt failed: {error.toMessageData}"
    saved.restore
  pure false

/-- Plan an AVATAR split before any definition is unfolded.

`avatar_split_clause` has two independently meaningful orders. The displayed
child AVATAR context is a set, so its order is immaterial. In contrast,
Vampire gives the definition parents in the order of the components in the
principal *regular* parent. We consume matching displayed AVATAR occurrences
in that definition-parent order to obtain `canonical`. This is the only list
that is expanded into regular literals later.

Existing AVATAR literals from the principal parent are removed first and
appended in their parent order. They are carried conditions rather than new
split components and are never expanded by this rule. Returning `none` means
that the displayed AVATAR context cannot be accounted for by those two parts. -/
private def planAvatarSplit (atoms : Array Expr) (parents : Array ParentProof)
    (targetAvatar : Array Expr) :
    MetaM (Option (Array Expr × Array Expr × Array Nat)) := do
  let carried := match parents[0]?.bind (·.clauseLiterals?) with
    | some parentLiterals =>
      (splitAClauseLiterals atoms parentLiterals).2
    | none => #[]
  -- A carried literal must occur in the child too. Exact matching preserves
  -- multiplicity even though the final A-clause semantics is set-like.
  let mut pendingCarried := carried.toList
  let mut remaining := targetAvatar.toList
  for literal in carried do
    let some index := remaining.findIdx? (· == literal) | return none
    remaining := remaining.eraseIdx index
    pendingCarried := pendingCarried.erase literal
  unless pendingCarried.isEmpty do return none
  let mut newInSourceOrder : Array Expr := #[]
  -- Alongside each selected AVATAR literal, retain the index of the
  -- definition parent which selected it. `post_rewrite_instantiation` names
  -- those parents, so this is the bridge from Vampire's certificate to the
  -- universal binders introduced when their components are expanded.
  let mut definitionParentIndices : Array Nat := #[]
  for parentIndex in [1:parents.size] do
    let some parent := parents[parentIndex]? | continue
    let definitionType := (← whnf parent.target).consumeMData
    unless definitionType.isAppOf ``Iff do continue
    let arguments := definitionType.getAppArgs
    let some split := arguments[arguments.size - 2]? | continue
    let mut occurrenceIndex := none
    for (literal, index) in remaining.zipIdx do
      if ← (pure (literal == split) <||> (do return (← notArgument? literal).any (· == split))) then
        occurrenceIndex := some index
        break
    let some index := occurrenceIndex | continue
    newInSourceOrder := newInSourceOrder.push remaining[index]!
    definitionParentIndices := definitionParentIndices.push parentIndex
    remaining := remaining.eraseIdx index
  unless remaining.isEmpty || newInSourceOrder.isEmpty do return none
  return some (newInSourceOrder ++ carried, carried, definitionParentIndices)

/-- A lookup key for a local binder named by an AVATAR split certificate.

The same definition node can occur in a split clause several times.  Its
variable spelling alone is therefore insufficient: `X0` from `f136` and `X0`
from another definition are unrelated binders.  A separator which cannot occur
in a TPTP identifier keeps the two parser names distinct without introducing a
new equality or hashing implementation for a pair of strings. -/
private def avatarSplitArgumentKey (definitionParent definitionVariable : String) : String :=
  definitionParent ++ "\x00" ++ definitionVariable

/-- Close an AVATAR split using Vampire's explicit post-rewrite binder map.

The ordinary AC path normalizes the universally quantified source before it
has been instantiated. Its term ordering then depends on *source* local
variables, which need not have the same order as the binders exposed by
`prenexify` on the expanded target. The `post_rewrite_instantiation` extra
certificate tells us which definition supplies every source variable.

Each expanded definition contributes one *block* of binders. For the
left-associated disjunction built by `avatarSplitClause`, `prenexify` puts the
first block first and then moves later blocks out from right to left; it keeps
the order *within* every block. We reproduce that documented shape, attach
each resulting fvar to its original `(definition node, binder name)`, and
consume exactly the bindings certified by Vampire. This handles both the
common one-binder definition and definitions such as
`spl ↔ ∀ X6 X0, component X6 X0`.

We first apply the source clause to those target fvars and only then call
`ac_nf0`. Both sides consequently contain exactly the same local variables,
so AC normalization is alpha-stable and `exact` checks the final result.
Repeated occurrences of one definition parent consume their complete binder
blocks in component order. They define identical components, and the
surrounding clause is AC-normalized, so exchanging such occurrences is
harmless but still fully checked by the final `exact`. -/
private def leadingForallCount (type : Expr) : MetaM Nat := do
  let mut current := type
  let mut count := 0
  let mut hasBinder := true
  while hasBinder do
    current ← whnf current
    if current.isForall then
      count := count + 1
      current := current.bindingBody!
    else
      hasBinder := false
  return count

/-- Use the certificate against an explicitly constructed universal prefix.
The new prefix follows component order, without relying on `prenexify`'s
normalization order. Failed attempts restore all goal/context assignments. -/
def closeAvatarGoalDirect (goal : MVarId) (source : Expr)
    (sourceBinders : Array FormulaBinder) (componentParents : Array ParentProof)
    (info : AvatarSplitInfo) : MetaM Bool := do
  let saved ← saveState
  let result ← try
    goal.withContext do
      let count := componentParents.foldl (fun n parent => n + parent.componentBinders.size) 0
      unless info.bindings.size == sourceBinders.size && count == sourceBinders.size do
        return false
      unless (sourceBinders.map (·.name)).toList.eraseDups.length == sourceBinders.size do
        return false
      let targetView ← AvatarPrenex.transform (← goal.getType)
      let sourceView ← AvatarPrenex.transform (← inferType source)
      let sourceProof ← mkAppM ``Iff.mp #[sourceView.equivalence, source]
      let newGoal ← mkFreshExprSyntheticOpaqueMVar targetView.formula
      let mut bodyGoal := newGoal.mvarId!
      let mut values : Array Expr := #[]
      for _ in [:count] do
        let type ← bodyGoal.withContext (whnf (← bodyGoal.getType))
        unless type.isForall do return false
        if ← bodyGoal.withContext (isProp type.bindingDomain!) then return false
        let (id, next) ← bodyGoal.intro1P
        values := values.push (mkFVar id)
        bodyGoal := next
      let closed ← bodyGoal.withContext do
        if let .forallE _ domain _ _ ← whnf (← bodyGoal.getType) then
          unless ← isProp domain do return false
        -- Repeated definition occurrences own distinct binder blocks. Each
        -- named argument queue must be consumed exactly once per occurrence.
        let mut arguments : Std.HashMap String (List Expr) := {}
        let mut index := 0
        for parent in componentParents do
          for binder in parent.componentBinders do
            let some value := values[index]? | return false
            let key := avatarSplitArgumentKey parent.parent.name binder.name
            arguments := arguments.insert key (arguments.getD key [] ++ [value])
            index := index + 1
        unless index == values.size do return false
        let mut assignments : Std.HashMap String Expr := {}
        for binding in info.bindings do
          if assignments.contains binding.sourceVariable then return false
          let key := avatarSplitArgumentKey binding.definitionParent binding.definitionVariable
          let some (value :: rest) := arguments.get? key | return false
          arguments := arguments.insert key rest
          assignments := assignments.insert binding.sourceVariable value
        unless arguments.toList.all (fun (_, queue) => queue.isEmpty) do return false
        let mut sourceInstance := sourceProof
        let mut type := sourceView.formula
        for binder in sourceBinders do
          let some value := assignments.get? binder.name | return false
          let .forallE _ domain inner _ ← whnf type | return false
          if ← isProp domain then return false
          unless ← isDefEq domain (← inferType value) do return false
          sourceInstance := mkApp sourceInstance value
          type := inner.instantiate1 value
        if let .forallE _ domain _ _ ← whnf type then
          unless ← isProp domain do return false
        let some proof ← AvatarPrenex.permuteClause
            (mkExpectedPropHint sourceInstance type) (← bodyGoal.getType) | return false
        bodyGoal.assign proof
        return true
      unless closed do return false
      let proof ← mkAppM ``Iff.mpr #[targetView.equivalence, (← instantiateMVars newGoal)]
      goal.assign proof
      return true
  catch _ => pure false
  unless result do saved.restore
  pure result

private def closeAvatarGoalByCertificate (goal : MVarId) (source : Expr)
    (sourceBinders : Array FormulaBinder) (componentParents : Array ParentProof)
    (info : AvatarSplitInfo) : MetaM Bool := do
  -- Fully check the parser-side shape before running `prenexify`: tactics
  -- change the local context, so a declined certificate path must be able to
  -- leave the original goal untouched for the ordinary AC fallback.
  let componentBinderCount := componentParents.foldl
    (fun count parent => count + parent.componentBinders.size) 0
  -- A split may mix quantified components with propositional ones (e.g.
  -- `sP3 ∨ ∀ x, C x`). A propositional component contributes an empty binder
  -- block, not a reason to reject the certificate. The total count and the
  -- subsequent named queue checks still certify every instantiated variable.
  unless !sourceBinders.isEmpty && !componentParents.isEmpty &&
      info.bindings.size == sourceBinders.size &&
      componentBinderCount == sourceBinders.size do
    return false
  let sourceDecl ← getFVarLocalDecl source
  let sourceName := sourceDecl.userName
  let prenexSource ← `(tactic| prenexify at $(mkIdent sourceName):ident)
  let (prenexedGoals, _) ← Lean.Elab.runTactic goal prenexSource
  let [initialTargetGoal] := prenexedGoals | return false
  let mut targetGoal := initialTargetGoal

  -- Open the target prefix ourselves. The returned fvars are the actual
  -- values with which the source theorem must be instantiated.
  let mut targetValues : Array Expr := #[]
  while true do
    let targetType ← whnf (← targetGoal.getType)
    unless targetType.isForall do break
    let (binder, nextGoal) ← targetGoal.intro1P
    targetValues := targetValues.push (mkFVar binder)
    targetGoal := nextGoal
  unless targetValues.size == componentBinderCount do return false

  -- Associate every definition occurrence with its *whole* target binder
  -- block. For a left-associated disjunction, VampLean leaves component zero
  -- first and pulls the remaining blocks out in reverse component order. The
  -- nested `for` retains each definition's own `∀ X₁ ... Xₙ` order.
  let mut componentValues : Array (Array Expr) :=
    Array.replicate componentParents.size #[]
  let mut nextTargetIndex := 0
  for placement in [:componentParents.size] do
    let componentIndex := if placement == 0 then 0 else componentParents.size - placement
    let some componentParent := componentParents[componentIndex]? | return false
    let binderCount := componentParent.componentBinders.size
    let mut values : Array Expr := #[]
    for offset in [:binderCount] do
      let some value := targetValues[nextTargetIndex + offset]? | return false
      values := values.push value
    componentValues := componentValues.set! componentIndex values
    nextTargetIndex := nextTargetIndex + binderCount
  unless nextTargetIndex == targetValues.size do return false

  -- A definition may be cited repeatedly. Keep a queue for each named
  -- `(definition node, component binder)` pair; the certificate consumes one
  -- fvar from its queue for every source-variable assignment.
  let mut valuesByArgument : Std.HashMap String (List Expr) := {}
  for componentIndex in [:componentParents.size] do
    let some componentParent := componentParents[componentIndex]? | return false
    let some values := componentValues[componentIndex]? | return false
    unless values.size == componentParent.componentBinders.size do return false
    for (binder, value) in componentParent.componentBinders.zip values do
      let key := avatarSplitArgumentKey componentParent.parent.name binder.name
      let existing := valuesByArgument.getD key []
      valuesByArgument := valuesByArgument.insert key (existing ++ [value])

  -- Consume the definition occurrences named by Vampire. The certificate is
  -- written by source-variable name, whereas applying the source theorem
  -- needs its original leading-binder order.
  let mut sourceValues : Std.HashMap String Expr := {}
  for binding in info.bindings do
    if sourceValues.contains binding.sourceVariable then return false
    let key := avatarSplitArgumentKey binding.definitionParent binding.definitionVariable
    match valuesByArgument.get? key with
    | some (value :: rest) =>
      valuesByArgument := valuesByArgument.insert key rest
      sourceValues := sourceValues.insert binding.sourceVariable value
    | _ => return false
  -- The certificate has the same cardinality as the target binder prefix.
  -- Requiring every queue to be empty additionally rejects a malformed
  -- annotation that duplicated one binder and omitted another.
  unless valuesByArgument.toList.all fun (_, values) => values.isEmpty do return false
  let mut sourceInstance := source
  for binder in sourceBinders do
    let some value := sourceValues.get? binder.name | return false
    sourceInstance := mkApp sourceInstance value
    try
      discard <| inferType sourceInstance
    catch _ => return false
  let sourceInstanceType ← inferType sourceInstance

  -- Store the specialized theorem in the local context. `ac_nf0` then sees
  -- the target fvars on both sides, unlike the unspecialized source theorem.
  let instanceName := `avatarSourceInstance
  targetGoal ← targetGoal.assert instanceName sourceInstanceType sourceInstance
  -- `MVarId.assert` turns the current target into an implication. Introduce
  -- its already supplied proof so the named local hypothesis is available to
  -- the following tactic block.
  let (_, targetGoalAfterInstance) ← targetGoal.intro1P
  targetGoal := targetGoalAfterInstance
  let finish ← `(tactic|
    (try simp only [eq_comm, ne_comm] at $(mkIdent instanceName):ident
     ac_nf0 at $(mkIdent instanceName):ident
     all_goals try simp only [eq_comm, ne_comm]
     all_goals ac_nf))
  let (remaining, _) ← Lean.Elab.runTactic targetGoal finish
  if remaining.isEmpty then return true
  let [remainingGoal] := remaining | return false
  remainingGoal.withContext do
    let currentInstance := (← getLocalDeclFromUserName instanceName).toExpr
    let target ← remainingGoal.getType
    unless ← isDefEq (← inferType currentInstance) target do
      trace[vampire.replay] "AVATAR split certificate normalization left:\nsource {← inferType currentInstance}\ntarget {target}"
      return false
    remainingGoal.assign currentInstance
    return true

/-- Replace the principal clause by its certified AVATAR components.
Transport the propositional split context before expanding definitions, then
recover universal arguments from the split certificate when needed. -/
def avatarSplitClause (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.step.binders.isEmpty &&
      !input.parents.isEmpty do return none
  let some targetLiterals := input.clauseLiterals? | return none
  let atoms := avatarAtoms input
  let (targetRegular, targetAvatar) := splitAClauseLiterals atoms targetLiterals
  -- This rule replaces a whole regular clause by split atoms.  Keep the
  -- first-order part out of this special handler: ordinary mixed A-clause
  -- inferences are reconstructed by the calculus handlers instead.
  unless targetRegular.isEmpty do return none

  let some (sourceOrderedAvatar, carriedAvatar, definitionParentIndices) ←
      planAvatarSplit atoms input.parents targetAvatar | return none
  let mut carried := carriedAvatar.toList
  let carriedCount := carried.length
  -- Choose the AVATAR-side transport target *before* unfolding a definition.
  -- The temporary list is source ordered, while `targetAvatar` remains the
  -- set-like TSTP result to which we transport after the regular proof.
  let mut mentionedSplits : Array Expr := #[]
  for literal in targetLiterals do
    if carried.contains literal then
      carried := carried.erase literal
      continue
    let atom ← if atoms.any (· == literal) then pure literal else
      match ← notArgument? literal with
      | some negated => pure negated
      | none => continue
    if atoms.any (· == atom) && !mentionedSplits.contains atom then
      mentionedSplits := mentionedSplits.push atom
  if mentionedSplits.isEmpty then return none

  try
    let proof ← withFormulaParents input.parents 0 #[] fun formulaParents => do
      -- Select precisely the definition hypotheses whose left side occurs as
      -- a split literal in the result. `formulaParents` has the same
      -- indexing as `input.parents`, including parents converted from clause
      -- form for this local tactic boundary.
      let mut rewriteProofs : Array Expr := #[]
      let mut rewrittenSplits : Array Expr := #[]
      for index in [:input.parents.size] do
        let some parent := input.parents[index]?
          | throwError "AVATAR split parent index is out of bounds"
        let definitionType := (← whnf parent.target).consumeMData
        unless definitionType.isAppOf ``Iff do continue
        let arguments := definitionType.getAppArgs
        let some split := arguments[arguments.size - 2]? | continue
        unless mentionedSplits.any (· == split) do continue
        -- Vampire may cite the same definition once per occurrence of a
        -- duplicated split literal. One rewrite proof rewrites every such
        -- occurrence in the target, so retain only its first citation.
        if rewrittenSplits.any (· == split) then continue
        let some formulaParent := formulaParents[index]?
          | throwError "missing ordinary formula view of an AVATAR split parent"
        rewriteProofs := rewriteProofs.push formulaParent
        rewrittenSplits := rewrittenSplits.push split
      unless rewriteProofs.size == mentionedSplits.size do
        throwError "AVATAR split does not cite one definition for every used split symbol"
      trace[vampire.replay] "AVATAR split {input.step.name}: rewriting {rewriteProofs.size} definition(s); carrying {carriedCount} parent AVATAR literal(s)"

      let canonicalAvatarList := mkPropList sourceOrderedAvatar.toList
      -- TPTP's parser preserves the displayed left-associated `|` tree.  The
      -- source parent has that tree too, so retain it while proving the
      -- expanded clause; `Clause.Holds` is introduced only afterward for the
      -- A-clause transport.
      let mut canonicalTarget? : Option Expr := none
      for literal in sourceOrderedAvatar do
        let canonicalTarget := match canonicalTarget? with
          | none => literal
          | some left => mkAppN (mkConst ``Or) #[left, literal]
        canonicalTarget? := some canonicalTarget
      let some canonicalTarget := canonicalTarget?
        | throwError "AVATAR split has no source-ordered split literals"
      -- The components are let-bound, so the split itself is a fixed
      -- refutation over the cited clause; see `Structural.splitClause`.
      -- The rewrite/prenex/AC tactic path below remains as the fallback.
      let structural? ← match formulaParents[0]? with
        | some source => Structural.splitClause source canonicalTarget (some mentionedSplits)
        | none => pure none
      if structural?.isSome then
        trace[vampire.replay] "AVATAR split {input.step.name}: structural refutation"
      let canonicalProof ← match structural? with
        | some proof => pure proof
        | none => do
          -- Hide the source facts (a proof-local Skolem `let` depending on one
          -- keeps it visible) and the stored clause hypotheses: their temporary
          -- ordinary-formula counterparts remain in scope and are the only parent
          -- forms consumed by the tactic below.
          let clauseParents := input.parents.filterMap fun parent =>
            if parent.clauseForm then parent.proof.fvarId? else none
          let goalExpr ← mkGoalWithout canonicalTarget (input.sourceFVars ++ clauseParents)
          let mut goal := goalExpr
          -- Rewrite the target directly with the selected local `Iff` proofs.
          -- This is the metaprogramming equivalent of
          -- `rw [definition₁, ...]`, without manufacturing tactic syntax for a
          -- dynamically sized list.
          for rewriteProof in rewriteProofs do
            let rewriteResult ← goal.rewrite (← goal.getType) rewriteProof
            unless rewriteResult.mvarIds.isEmpty do
              throwError "rewriting an AVATAR definition created unresolved goals"
            goal ← goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof
          -- Try the explicit binder transport and occurrence permutation
          -- before invoking the general prenex/AC tactics.
          let mut directComponents : Array ParentProof := #[]
          for parentIndex in definitionParentIndices do
            let some parent := input.parents[parentIndex]?
              | throwError "AVATAR split definition-parent index is out of bounds"
            directComponents := directComponents.push parent
          let directClosed ← if let some certificate := input.step.inference?.bind Inference.avatarSplit? then do
            let some principal := input.parents[0]? | throwError "missing AVATAR principal parent"
            let some source := formulaParents[0]? | throwError "missing AVATAR principal formula"
            let closed ← closeAvatarGoalDirect goal source principal.binders directComponents certificate
            if closed then
              trace[vampire.replay] "AVATAR split {input.step.name}: direct certificate transport"
            pure closed
          else pure false
          unless directClosed do
            -- Rewriting definitions introduces independent universal blocks in the
            -- target.  Use VampLean's normal prenex pass, just as the generated
            -- paper-style proof scripts do.  The principal source is normalized by
            -- `closeAvatarGoalByAC` below.
            let tactic ← `(tactic| prenexify)
            let (remaining, _) ← Lean.Elab.runTactic goal tactic
            unless remaining.isEmpty do
              let [normalizedGoal] := remaining
                | throwError "AVATAR split prenexing created multiple goals"
              let some source := formulaParents[0]?
                | throwError "AVATAR split has no principal source clause"
              -- When Vampire was invoked with `--proof_extra avatar_split`, use its
              -- post-rewrite binder certificate before falling back to the simpler
              -- AC-only path. `definitionParentIndices` is aligned with the fresh
              -- source-ordered split occurrences selected in `planAvatarSplit`.
              let mut componentParents : Array ParentProof := #[]
              for parentIndex in definitionParentIndices do
                let some parent := input.parents[parentIndex]?
                  | throwError "AVATAR split definition-parent index is out of bounds"
                componentParents := componentParents.push parent
              let some principalParent := input.parents[0]?
                | throwError "AVATAR split has no principal parent"
              let certificate? := input.step.inference?.bind Inference.avatarSplit?
              let closedByCertificate ← match certificate? with
                | some certificate =>
                  -- Do not enter the certificate tactic unless the parser-side
                  -- component prefixes account for every displayed target binder.
                  -- The tactic changes local hypotheses, so this check must happen
                  -- before it starts; unsupported shapes continue through the general
                  -- AC path below without a partially changed local context.
                  let targetBinderCount ← leadingForallCount (← normalizedGoal.getType)
                  let componentBinderCount := componentParents.foldl
                    (fun count parent => count + parent.componentBinders.size) 0
                  if certificate.bindings.size == principalParent.binders.size &&
                      componentBinderCount == certificate.bindings.size &&
                      targetBinderCount == componentBinderCount then
                    closeAvatarGoalByCertificate normalizedGoal source principalParent.binders
                      componentParents certificate
                  else
                    pure false
                | none => pure false
              let closed ← if closedByCertificate then pure true else
                closeAvatarGoalByAC normalizedGoal source
              unless closed do
                throwError "AVATAR split could not match the prenexed source clause"
          instantiateMVars (.mvar goalExpr)
      unless (← instantiateMVars (← inferType canonicalProof)) == canonicalTarget do
        throwError "AVATAR split proof does not have the canonical target type"
      -- `canonicalTarget` is the left-nested `Or` of `sourceOrderedAvatar`, so
      -- this syntactic tree denotes it and its literals are exactly that list.
      -- Applying the theorems directly and stating the known list avoids
      -- unifying `Tree.denote`/`Tree.literals` by reduction; the kernel still
      -- checks both conversions.
      let leaves := sourceOrderedAvatar.map (mkApp (mkConst ``VampireHammer.Clause.Tree.atom))
      let canonicalTree := leaves.foldl (init := leaves[0]!) (start := 1)
        (mkApp2 (mkConst ``VampireHammer.Clause.Tree.join))
      let canonicalClause := mkExpectedPropHint
        (mkApp2 (mkConst ``VampireHammer.Clause.Tree.toHolds) canonicalTree canonicalProof)
        (mkApp (mkConst ``VampireHammer.Clause.Holds) canonicalAvatarList)
      let emptyList := mkPropList ([] : List Expr)
      let canonicalAClause := mkApp3 (mkConst ``VampireHammer.Clause.AClause.fromClause)
        emptyList canonicalAvatarList canonicalClause
      let some targetAClause ← transportAvatarSet canonicalAClause #[] sourceOrderedAvatar targetAvatar
        | throwError "AVATAR split could not transport its AVATAR context"
      -- Keep the already checked A-clause. The replay boundary accepts it
      -- directly, avoiding AClause → Clause → formula → AClause conversions.
      pure targetAClause
    pure (some proof)
  catch error =>
    trace[vampire.replay] "AVATAR split {input.step.name} declined: {error.toMessageData}"
    pure none

end VampireHammer.Backend

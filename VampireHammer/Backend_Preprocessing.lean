import VampireHammer.Clause_Meta
import VampireHammer.Backend_Structural
import VampireHammer.Backend.Types
import VampLean
import Auto.Tactic

/-!
Proof reconstruction for Vampire's logical preprocessing rules.

VampLean supplies the trusted transformations themselves.  This module runs
the corresponding tactic on the one cited parent hypothesis and then proves
the exact formula printed by Vampire.  CNF is slightly different: `cnfify`
turns its parent into a conjunction of clauses, while Vampire emits a separate
proof node for each selected clause.  The CNF selector below traverses that
conjunction, compares literal multisets, and constructs an explicit
`Clause.reorder` proof when Vampire chose another literal order.
-/

namespace VampireHammer.BackendPreprocessing

open Lean Meta Elab Tactic
open VampireHammer.ClauseMeta

/-- The preprocessing information independent of the parser AST. -/
structure Input where
  stepName : String
  rule : String
  target : Expr
  /-- TPTP names of the conclusion's leading universal binders, in the order
  printed by Vampire.  Vampire may reorder this list during CNF conversion. -/
  targetBinders : Array String
  /-- TPTP names of the cited parent's leading universal binders.  A CNF
  candidate produced from that parent still expects arguments in this order,
  even when the child prints the same binders in another order. -/
  parentBinders : Array String
  parentProof : Expr
  cnfCertificate? : Option VampireHammer.Backend.CnfCertificate := none
  /-- Proofs of the conjuncts in the parent's CNF result, computed on demand
  as a fallback for `directCnf`.  `Replay` runs `cnfify` and splits the result
  once per proof-DAG parent and shares it with every `cnf_transformation`
  child. -/
  cnfCandidates : MetaM (Option (Array (Expr × Expr))) := pure none

/-- Recognize `Or left right` after reducible wrappers are unfolded. -/
private def orArguments? (formula : Expr) : MetaM (Option (Expr × Expr)) := do
  let formula ← whnf formula
  match formula with
  | .app (.app (.const ``Or _) left) right => pure (some (left, right))
  | _ => pure none

/-- Flatten a clause to its ordered literal occurrences.  `False` denotes the
empty clause, and all non-`Or` propositions, including negations, are atoms. -/
private partial def flattenClause (formula : Expr) : MetaM (Array Expr) := do
  let formula ← whnf formula
  if formula.isConstOf ``False then return #[]
  match ← orArguments? formula with
  | some (left, right) => return (← flattenClause left) ++ (← flattenClause right)
  | none => return #[formula]

/-- Reify the concrete `Or` grouping so `Clause.Tree.toHolds` and
`Clause.Tree.fromHolds` can cross the formula/list boundary. -/
private partial def clauseTree (formula : Expr) : MetaM Expr := do
  let formula ← whnf formula
  if formula.isConstOf ``False then
    pure (mkConst ``VampireHammer.Clause.Tree.empty)
  else
    match ← orArguments? formula with
    | none => pure (mkAppN (mkConst ``VampireHammer.Clause.Tree.atom) #[formula])
    | some (left, right) =>
      pure (mkAppN (mkConst ``VampireHammer.Clause.Tree.join)
        #[← clauseTree left, ← clauseTree right])

/-- Split the conjunction produced by `cnfify` and retain a proof for every
leaf clause.  Association of `And` is irrelevant because every leaf is
visited. -/
private partial def conjunctionLeaves (proof type : Expr) :
    MetaM (Array (Expr × Expr)) := do
  -- Try the syntactic shape first; `whnf` is needed only for a conjunction
  -- hidden behind a definition.  The projections are built directly from
  -- the known conjuncts: `mkAppM` would re-infer the type of the growing
  -- projection term at every node.
  let type := type.consumeMData
  let type ← if type.isAppOfArity ``And 2 then pure type else whnf type
  match type with
  | .app (.app (.const ``And _) left) right =>
    let leftProof := mkApp3 (mkConst ``And.left) left right proof
    let rightProof := mkApp3 (mkConst ``And.right) left right proof
    return (← conjunctionLeaves leftProof left) ++
      (← conjunctionLeaves rightProof right)
  | _ => pure #[(proof, type)]

/-- Ask a VampLean hypothesis-transforming tactic to synthesize a reusable
theorem.  The result proposition starts as a metavariable and is fixed by the
transformed hypothesis supplied to `exact`.

For example, with `transformation = cnfify at h`, the returned expression has
type `parent → cnf(parent)`.  It contains no particular proof-DAG parent and
can therefore be applied to every fresh local copy of that parent. -/
private inductive Transformation where
  | cnf
  | prenex
  | flatten
  | removeTauto
  | ennf
  | nnf

private def transformationLemma (source : Expr)
    (transformation : Transformation) : MetaM (Option Expr) := do
  let resultType ← mkFreshExprMVar (mkSort Level.zero)
  let theoremType := mkForall `vampireTransformParent .default source resultType
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar theoremType | return none
  let tactic ← match transformation with
    | .cnf => `(tactic|
      (intro vampireTransformParent;
       cnfify at vampireTransformParent;
       exact vampireTransformParent))
    | .prenex => `(tactic|
      (intro vampireTransformParent;
       prenexify at vampireTransformParent;
       exact vampireTransformParent))
    | .flatten => `(tactic|
      (intro vampireTransformParent;
       flattening at vampireTransformParent;
       exact vampireTransformParent))
    | .removeTauto => `(tactic|
      (intro vampireTransformParent;
       remove_tauto at vampireTransformParent;
       exact vampireTransformParent))
    | .ennf => `(tactic|
      (intro vampireTransformParent;
       ennf_transformation at vampireTransformParent;
       exact vampireTransformParent))
    | .nnf => `(tactic|
      (intro vampireTransformParent;
       nnf_transformation at vampireTransformParent;
       exact vampireTransformParent))
  try
    let (remaining, _) ← Lean.Elab.runTactic goal tactic
    unless remaining.isEmpty do return none
    let proof ← instantiateMVars (.mvar goal)
    unless ← isTypeCorrect proof do return none
    pure (some proof)
  catch _ =>
    pure none

/-- Whether `body` contains no quantifier.  A `forallE` whose domain mentions
a bound variable, or is a proposition, is an implication (such as the
`p → False` of a negated literal) rather than a quantifier. -/
private partial def isQuantifierFree (body : Expr) : MetaM Bool := do
  match body with
  | .forallE _ domain rest _ =>
    if !domain.hasLooseBVars then
      unless ← isProp domain do return false
    unless ← isQuantifierFree domain do return false
    isQuantifierFree rest
  | .app function argument =>
    if body.isAppOf ``Exists then return false
    unless ← isQuantifierFree function do return false
    isQuantifierFree argument
  | .lam _ _ rest _ => isQuantifierFree rest
  | .mdata _ inner => isQuantifierFree inner
  | .letE .. => return false
  | _ => pure true

/-- Whether a clause is already in prenex form: leading universals over a
quantifier-free body. -/
private partial def isPrenexClause (type : Expr) : MetaM Bool := do
  if let .forallE name domain body _ := type then
    unless ← isProp domain do
      return ← withLocalDeclD name domain fun binder =>
        isPrenexClause (body.instantiate1 binder)
  isQuantifierFree type

/-- Prenex one selected conjunction leaf before clause comparison.  This is
the programmatic analogue of `prenexify at s953c0` in the paper-generated
proof. -/
private def prenexCandidate (proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← inferType proof
  -- Most `cnfify` leaves are already prenex clauses; running the tactic on
  -- them is the dominant cost of CNF preparation.
  if ← isPrenexClause (← Core.betaReduce (← instantiateMVars type)) then
    return some (proof, type)
  let some lemma ← transformationLemma type .prenex
    | return none
  let transformed := mkApp lemma proof
  pure (some (transformed, ← inferType transformed))

/-- Run `cnfify` once for one concrete proof-DAG parent and split the resulting
conjunction once.

This is the metaprogramming equivalent of the paper's

```lean
let step953' := by
  cnfify at step953
  exact step953
let ⟨s953c0, s953c1, ...⟩ := step953'
```

The returned pairs contain each conjunct proof and its proposition.  Replay
caches the whole array under the parent node name, so sibling Vampire steps do
not rerun either `cnfify` or conjunction elimination. -/
def prepareCnf (parentProof : Expr) : MetaM (Option (Array (Expr × Expr))) :=
  Meta.withNewMCtxDepth do
    let some lemma ← transformationLemma (← inferType parentProof) .cnf
      | return none
    let cnfProof := mkApp lemma parentProof
    -- Prenex every leaf once here: the result is cached per parent, whereas
    -- each sibling CNF step would otherwise prenex every leaf again.
    let leaves ← conjunctionLeaves cnfProof (← instantiateMVars (← inferType cnfProof))
    pure (some (← leaves.filterMapM fun (proof, _) => prenexCandidate proof))

/-- A key for a literal that does not depend on how variables are assigned:
its polarity and head symbol (equalities share one key, since either side
may be printed first).  Equal clauses up to permutation have equal key
multisets, so differing multisets reject a candidate cheaply. -/
private partial def literalKey (literal : Expr) : MetaM String := do
  let literal ← whnfR literal.consumeMData
  if let some inner := literal.not? then
    return "¬" ++ (← literalKey inner)
  if let .forallE _ domain body _ := literal then
    if body.consumeMData.isConstOf ``False && !body.hasLooseBVars then
      return "¬" ++ (← literalKey domain)
  if literal.isAppOfArity ``Eq 3 then return "="
  match literal.getAppFn with
  | .fvar fvarId => return s!"{fvarId.name}/{literal.getAppNumArgs}"
  | .const name _ => return s!"{name}/{literal.getAppNumArgs}"
  | _ => return "?"

/-- Sorted literal keys of a clause body. -/
private def clauseKeys (body : Expr) : MetaM (Array String) := do
  let keys ← (← flattenClause body).mapM literalKey
  pure (keys.qsort (· < ·))

/-- The number of leading first-order binders and the sorted literal keys of
the clause below them.  A binder over a proposition (the `p → False` of a
negated literal) is not a clause variable. -/
private partial def clauseShape (type : Expr) : MetaM (Nat × Array String) := do
  let type ← whnf type
  if let .forallE name domain body _ := type then
    unless ← isProp domain do
      return ← withLocalDeclD name domain fun binder => do
        let (binders, keys) ← clauseShape (body.instantiate1 binder)
        pure (binders + 1, keys)
  pure (0, ← clauseKeys type)

/-- Instantiate one candidate clause's leading universals with the variables
opened from Vampire's target.  Exact arity and domain checks keep this search
from treating a logical implication as another first-order binder. -/
private def instantiateCandidate (proof : Expr) (variables : Array Expr) :
    MetaM (Option (Expr × Expr)) := do
  let mut proof := proof
  let mut type ← inferType proof
  for argument in variables do
    type ← whnf type
    unless type.isForall do return none
    unless ← isDefEq type.bindingDomain! (← inferType argument) do return none
    proof := mkApp proof argument
    type := type.bindingBody!.instantiate1 argument
  pure (some (proof, type))

/-- Convert a candidate formula proof to the exact target clause, allowing
only a permutation of literal occurrences. -/
private def reorderCandidate (proof source target : Expr) : MetaM (Option Expr) := do
  -- The common case needs no clause machinery at all. Apart from producing a
  -- much smaller term, this ensures an identity literal order does not appear
  -- as a synthetic permutation in the reconstructed proof.
  if ← isDefEq source target then
    return some proof
  let sourceLiterals ← flattenClause source
  let targetLiterals ← flattenClause target
  let sourceTree ← clauseTree source
  let targetTree ← clauseTree target
  let sourceClause ← mkAppM ``VampireHammer.Clause.Tree.toHolds #[sourceTree, proof]
  let some normalized ← reorderAndNormalize sourceClause sourceLiterals.toList targetLiterals.toList
    | return none
  let result ← mkAppM ``VampireHammer.Clause.Tree.fromHolds #[targetTree, normalized]
  unless ← isDefEq (← inferType result) target do return none
  pure (some result)

/-- Instantiate a prenexed CNF candidate with a subset and permutation of the
variables opened from the target, then compare the resulting clause with the
target.

The subset is important.  `cnfify` may turn `∀ x, P x ∧ Q` into the two
leaves `∀ x, P x` and `Q`; the second leaf no longer has a binder for `x`.
The permutation is equally important because Vampire may print the remaining
binders in a different order.  We accept an assignment only after
`reorderCandidate` has checked the complete resulting clause, so trying all
well-typed assignments cannot silently change the meaning of a certificate. -/
private partial def instantiateCandidateSearch (proof type target : Expr)
    (available : Array Expr) (used : Array Nat := #[]) : MetaM (Option Expr) := do
  let type ← whnf type
  if !type.isForall then
    return ← reorderCandidate proof type target
  for index in [:available.size] do
    if used.contains index then continue
    let result ← Meta.withNewMCtxDepth do
      let argument := available[index]!
      unless ← isDefEq type.bindingDomain! (← inferType argument) do
        return none
      instantiateCandidateSearch (mkApp proof argument)
        (type.bindingBody!.instantiate1 argument) target available (used.push index)
    if result.isSome then return result
  pure none

/-- If the parent and target retained exactly the same named binders, arrange
the opened target variables in the order expected by a candidate derived from
the parent.  This is the cheap and deterministic path for the common case;
CNF leaves that dropped unused binders use `instantiateCandidateSearch`. -/
private def parentArgumentsByName (opened : Array (String × Expr))
    (targetBinders parentBinders : Array String) : Option (Array Expr) := do
  guard (opened.size == targetBinders.size && parentBinders.size == targetBinders.size)
  parentBinders.mapM fun parentName => do
    let binding ← opened.find? (fun binding => binding.1 == parentName)
    pure binding.2

/-- Search every `cnfify` conjunct for Vampire's displayed clause.

`opened` records target variables by their TPTP names.  This distinction is
essential because Vampire can print a child prefix such as `[X2,X0,X1]` for a
parent whose prefix was `[X0,X1,X2]`.  The candidate proof was derived from
the parent and must therefore be applied in *parent* order; applying the
target variables positionally silently changes the clause. -/
private partial def findCnfClause (candidates : Array (Expr × Expr)) (target : Expr)
    (targetBinders parentBinders : Array String)
    (opened : Array (String × Expr) := #[]) : MetaM (Option Expr) := do
  if opened.size < targetBinders.size then
    let target ← whnf target
    unless target.isForall do return none
    let some binderName := targetBinders[opened.size]? | return none
    -- A repeated name would make the parent-to-target lookup ambiguous.  TFF
    -- quantifier lists should not contain one, so reject such a certificate.
    if opened.any (fun binding => binding.1 == binderName) then return none
    withLocalDeclD target.bindingName! target.bindingDomain! fun argument => do
      let some body ← findCnfClause candidates
        (target.bindingBody!.instantiate1 argument) targetBinders parentBinders
        (opened.push (binderName, argument)) | return none
      pure (some (← mkLambdaFVars #[argument] body))
  else
    unless opened.size == targetBinders.size do return none
    let namedArguments? := parentArgumentsByName opened targetBinders parentBinders
    let available := opened.map Prod.snd
    let targetKeys ← clauseKeys target
    for (candidateProof, candidateType) in candidates do
      -- A permutation preserves the multiset of literal keys, and a candidate
      -- cannot use more variables than the target binds.  Rejecting other
      -- leaves here avoids the instantiation search and the clause bridge.
      let (candidateBinders, candidateKeys) ← clauseShape candidateType
      unless candidateKeys == targetKeys && candidateBinders ≤ available.size do
        continue
      -- When no variables disappeared during CNF conversion, use the TPTP
      -- names to avoid a factorial search and to preserve the parent's binder
      -- meaning across a target-prefix permutation.
      if let some namedArguments := namedArguments? then
        let direct? ← Meta.withNewMCtxDepth do
          let some (proof, type) ← instantiateCandidate candidateProof namedArguments
            | return none
          reorderCandidate proof type target
        if direct?.isSome then return direct?
      -- A conjunct may omit one or more parent variables.  Its proof then has
      -- fewer leading `∀`s, so the full name vector is inapplicable.  Search
      -- the remaining well-typed assignments and validate the complete clause.
      let searched? ← Meta.withNewMCtxDepth <|
        instantiateCandidateSearch candidateProof candidateType target available
      if searched?.isSome then return searched?
    pure none

/-- Adapt a transformed formula to Vampire's concrete spelling below its
leading universal binders.  VampLean's normal-form tactics may leave a clause
with a different `Or` association, literal order, or equality orientation;
`reorderCandidate` turns that trusted result into the displayed clause using
the explicit clause bridge rather than asking `grind` to rediscover it. -/
private partial def adaptTransformation (proof target : Expr) (binderCount : Nat) :
    MetaM (Option Expr) := do
  if binderCount == 0 then
    return ← reorderCandidate proof (← inferType proof) target
  let source ← whnf (← inferType proof)
  let target ← whnf target
  unless source.isForall && target.isForall do return none
  unless ← isDefEq source.bindingDomain! target.bindingDomain! do return none
  withLocalDeclD target.bindingName! target.bindingDomain! fun binder => do
    let some body ← adaptTransformation (mkApp proof binder)
      (target.bindingBody!.instantiate1 binder) (binderCount - 1)
      | return none
    pure (some (← mkLambdaFVars #[binder] body))

/-- Transport `proof` to `target` when the two propositions differ only in the
orientation of equalities (and bound-variable names), using VampLean's
structural `symm_match`.  Connective grouping must already agree: the decoder
right-associates `∨`/`∧` in formula steps, matching Lean's notation. -/
def symmMatch (proof target : Expr) : MetaM (Option Expr) := do
  let source ← inferType proof
  if ← isDefEq source target then
    trace[vampire.replay] "symmMatch: types are definitionally equal"
    return some proof
  if let some result ← Structural.transport proof target then
    trace[vampire.replay] "structural transport replaced `symmMatch`"
    return some result
  let theoremType := mkForall `vampireSymmSource .default source target
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar theoremType | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro vampireSymmSource;
       symm_match using vampireSymmSource)))
    unless remaining.isEmpty do return none
    pure (some (mkApp (← instantiateMVars (.mvar goal)) proof))
  catch error =>
    trace[vampire.replay] "symm_match failed: {error.toMessageData}"
    pure none

/-- Prove `target` from `proof` when the two differ only in the grouping of
`∨`/`∧`, double negations, or propositional equality versus equivalence.
Used solely at the input boundary: TPTP's
`|` and `&` are n-ary, so an exported fact's Lean grouping is not represented
in Vampire's proof, Vampire prints an input `¬¬P` as `P`, and proposition
equality is encoded as equivalence. -/
def regroup (proof target : Expr) : MetaM (Option Expr) := do
  let source ← inferType proof
  if ← isDefEq source target then return some proof
  if let some result ← Structural.transport proof target then
    trace[vampire.replay] "structural transport replaced `regroup`"
    return some result
  let theoremType := mkForall `vampireRegroupSource .default source target
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar theoremType | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro vampireRegroupSource;
       simp only [or_assoc, and_assoc, Classical.not_not] at vampireRegroupSource ⊢;
       exact vampireRegroupSource)))
    unless remaining.isEmpty do return none
    pure (some (mkApp (← instantiateMVars (.mvar goal)) proof))
  catch error =>
    trace[vampire.replay] "regroup failed: {error.toMessageData}"
    pure none

/-- Like `symmMatch`, but first right-associates `∨`/`∧` on both sides.  Only
for proofs that are *constructed* with a different grouping than the target
(a named predicate's definition); never for matching Vampire's output. -/
def assocSymmMatch (proof target : Expr) : MetaM (Option Expr) := do
  let source ← inferType proof
  if ← isDefEq source target then return some proof
  if let some result ← Structural.transport proof target then
    trace[vampire.replay] "structural transport replaced `assocSymmMatch`"
    return some result
  let theoremType := mkForall `vampireAssocSymmSource .default source target
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar theoremType | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro vampireAssocSymmSource;
       try simp only [or_assoc, and_assoc] at vampireAssocSymmSource ⊢;
       symm_match using vampireAssocSymmSource)))
    unless remaining.isEmpty do return none
    pure (some (mkApp (← instantiateMVars (.mvar goal)) proof))
  catch error =>
    trace[vampire.replay] "assocSymmMatch failed: {error.toMessageData}"
    pure none

/-- Restate VampLean's `Xor' a b` as `¬(a ↔ b)`, the form the proof decoder
gives Vampire's `<~>`.  `none` when the proof mentions no `Xor'`. -/
private def xorAsNotIff (proof : Expr) : MetaM (Option Expr) := do
  let source ← instantiateMVars (← inferType proof)
  if (source.find? (·.isConstOf ``VampLean.Xor')).isNone then return none
  let target := source.replace fun e =>
    if e.isAppOfArity ``VampLean.Xor' 2 then
      some (mkNot (mkApp2 (mkConst ``Iff) e.appFn!.appArg! e.appArg!))
    else none
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar (mkForall `vampireXorSource .default source target)
    | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro vampireXorSource; simpa only [VampLean.not_iff_xor] using vampireXorSource)))
    unless remaining.isEmpty do return none
    pure (some (mkApp (← instantiateMVars (.mvar goal)) proof))
  catch error =>
    trace[vampire.replay] "xorAsNotIff failed: {error.toMessageData}"
    pure none

/-- Reconstruct a non-CNF VampLean preprocessing step.  Unlike the original
direct-goal version, this first synthesizes the transformation's own result
and only then adapts its clause presentation to Vampire's target. -/
private def runVampLean (input : Input) : MetaM (Option Expr) := do
  let transformation ← match input.rule with
    | "flattening" => pure Transformation.flatten
    | "remove_tauto" | "remove_tautologies" => pure Transformation.removeTauto
    | "ennf_transformation" => pure Transformation.ennf
    | "nnf_transformation" => pure Transformation.nnf
    | _ => return none
  if let some result ← Structural.transport input.parentProof input.target then
    trace[vampire.replay] "structural transport reconstructed {input.stepName} (`{input.rule}`)"
    return some result
  let some lemma ← transformationLemma (← inferType input.parentProof) transformation
    | trace[vampire.replay] "VampLean could not construct `{input.rule}` for {input.stepName}"
      return none
  let transformed := mkApp lemma input.parentProof
  let result ← adaptTransformation transformed input.target input.targetBinders.size
  if result.isSome then
    trace[vampire.replay] "VampLean reconstructed {input.stepName} with `{input.rule}`"
    return result
  -- Vampire may print an equality with its sides swapped (for example a
  -- negated equation after `ennf_transformation`), also inside a literal
  -- where the clause bridge in `adaptTransformation` does not reach.
  if let some result ← symmMatch transformed input.target then
    trace[vampire.replay] "VampLean reconstructed {input.stepName} with `{input.rule}` up to equality orientation"
    return result
  -- VampLean states `<~>` as `Xor'`; the decoder reads it as `¬(↔)`.
  if let some transformed ← xorAsNotIff transformed then
    if let some result ← adaptTransformation transformed input.target input.targetBinders.size then
      trace[vampire.replay] "VampLean reconstructed {input.stepName} with `{input.rule}` up to `Xor'`"
      return result
    if let some result ← symmMatch transformed input.target then
      trace[vampire.replay] "VampLean reconstructed {input.stepName} with `{input.rule}` up to `Xor'` and equality orientation"
      return result
  trace[vampire.replay] "VampLean `{input.rule}` could not adapt {input.stepName} after {input.targetBinders.size} leading binder(s):\nsource {← inferType transformed}\ntarget {input.target}"
  pure none

/-! ### Direct clause extraction for `cnf_transformation`

Vampire clausifies a formula that is already in NNF and flattened: it is
built from `∧`, `∨`, `∀` and literals.  Every clause of its CNF picks one side
of each `∧` and keeps both sides of each `∨`.  Instead of computing the whole
CNF with `cnfify` and searching it, we prove the displayed clause directly,
guided by the target:

* `A ∧ B` — prove the clause from `A` (via `And.left`), otherwise from `B`;
* `A ∨ B` — `Or.elim`, proving the clause from both branches;
* `∀ x, A` — instantiate `x` with a target variable of the same type;
* a literal — inject it into the target disjunction at a matching position,
  up to the orientation of an equality.

The proof uses only these eliminations and introductions, no tactic. -/

/-- Beta-reduce at the head until no redex is left there.  `Expr.headBeta`
alone stops after one step, but lean-auto's translation nests its binder
wrappers: reducing `(fun x => (fun p => ∀ y, p y) B) a` exposes a new redex. -/
private partial def headBetaAll (e : Expr) : Expr :=
  let reduced := e.headBeta.consumeMData
  if reduced == e then e else headBetaAll reduced

/-- The proposition negated by `literal`, if it is a negation. -/
private def negatedLiteral? (literal : Expr) : Option Expr :=
  match literal.consumeMData with
  | .app (.const ``Not _) inner => some inner
  | .forallE _ domain body _ =>
    if body.consumeMData.isConstOf ``False && !body.hasLooseBVars then some domain else none
  | _ => none

/-- Two equations with swapped sides. -/
private def swappedEquations (source target : Expr) : MetaM Bool := do
  let some (_, left, right) := source.consumeMData.eq? | return false
  let some (_, left', right') := target.consumeMData.eq? | return false
  unless ← isDefEq left right' do return false
  isDefEq right left'

/-- Convert `proof : source` to a proof of `target`, for literals that agree
up to definitional equality and the orientation of an (in)equality. -/
private def literalConversion (proof source target : Expr) : MetaM (Option Expr) := do
  if ← isDefEq source target then return some proof
  if ← swappedEquations source target then
    return some (← mkEqSymm proof)
  let some sourceAtom := negatedLiteral? source | return none
  let some targetAtom := negatedLiteral? target | return none
  unless ← swappedEquations sourceAtom targetAtom do return none
  withLocalDeclD `vampireCnfEquation targetAtom fun equation => do
    some <$> mkLambdaFVars #[equation] (mkApp proof (← mkEqSymm equation))

/-- Prove the clause `body` from `proof : literal` by injecting the literal
into a matching disjunct. -/
private partial def injectLiteral (body literal proof : Expr) : MetaM (Option Expr) := do
  match headBetaAll (← instantiateMVars body) with
  | .app (.app (.const ``Or _) left) right =>
    if let some leftProof ← injectLiteral left literal proof then
      return some (mkApp3 (mkConst ``Or.inl) left right leftProof)
    if let some rightProof ← injectLiteral right literal proof then
      return some (mkApp3 (mkConst ``Or.inr) left right rightProof)
    return none
  | disjunct => literalConversion proof literal disjunct

/-- Prove the clause `body` from `proof : formula`.  `preferred` lists the
target variable to try first for each leading universal of the parent: the
one Vampire printed under the same name. -/
private partial def proveClause (body : Expr) (variables : Array Expr)
    (formula proof : Expr) (preferred : List (Option Expr)) : MetaM (Option Expr) := do
  let formula := headBetaAll (← instantiateMVars formula)
  match formula with
  | .app (.app (.const ``And _) left) right =>
    if let some leftProof ← proveClause body variables left
        (mkApp3 (mkConst ``And.left) left right proof) [] then
      return some leftProof
    proveClause body variables right (mkApp3 (mkConst ``And.right) left right proof) []
  | .app (.app (.const ``Or _) left) right =>
    let some leftCase ← withLocalDeclD `vampireCnfLeft left fun hypothesis => do
        let some caseProof ← proveClause body variables left hypothesis [] | return none
        some <$> mkLambdaFVars #[hypothesis] caseProof
      | return none
    let some rightCase ← withLocalDeclD `vampireCnfRight right fun hypothesis => do
        let some caseProof ← proveClause body variables right hypothesis [] | return none
        some <$> mkLambdaFVars #[hypothesis] caseProof
      | return none
    return some (mkApp6 (mkConst ``Or.elim) left right body proof leftCase rightCase)
  | .const ``False _ => return some (mkApp2 (mkConst ``False.elim [Level.zero]) body proof)
  | .forallE _ domain inner _ =>
    if negatedLiteral? formula |>.isSome then
      return ← injectLiteral body formula proof
    if ← isProp domain then return none
    let (first?, rest) := match preferred with
      | first :: rest => (first, rest)
      | [] => (none, [])
    let mut choices := first?.toArray
    for candidate in variables do
      unless choices.contains candidate do choices := choices.push candidate
    -- A variable absent from the displayed clause still needs a witness, even
    -- when other conjuncts of the parent mention it (`∀ x, ¬q ∧ p x` ⊢ `¬q`).
    -- Any inhabitant of the domain will do: the first local of that type.
    if ← choices.allM fun choice => return !(← isDefEq (← inferType choice) domain) then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        if ← isDefEq decl.type domain then
          choices := choices.push decl.toExpr
          break
    for choice in choices do
      unless ← isDefEq (← inferType choice) domain do continue
      if let some result ← proveClause body variables (inner.instantiate1 choice)
          (mkApp proof choice) rest then
        return some result
    return none
  | _ => injectLiteral body formula proof

/-- Inject at a certified occurrence, retaining the target's exact grouping. -/
private partial def injectOccurrence (body : Expr) (index : Nat) (proof : Expr) :
    MetaM Expr := do
  match headBetaAll body with
  | .app (.app (.const ``Or _) left) right =>
    let count := (← flattenClause left).size
    if index < count then
      return mkApp3 (mkConst ``Or.inl) left right (← injectOccurrence left index proof)
    return mkApp3 (mkConst ``Or.inr) left right (← injectOccurrence right (index - count) proof)
  | _ =>
    unless index == 0 do throwError "CNF occurrence is out of bounds"
    pure proof

/-- A swap annotation certifies an equality orientation change, including
under negation; it cannot justify an arbitrary literal equivalence. -/
private def certifiedLiteral (source target proof : Expr) (swap : Bool) :
    MetaM (Option Expr) := do
  if !swap then
    if ← isDefEq source target then return some proof
    return none
  if ← swappedEquations source target then return some (← mkEqSymm proof)
  let some sourceAtom := negatedLiteral? source | return none
  let some targetAtom := negatedLiteral? target | return none
  unless ← swappedEquations sourceAtom targetAtom do return none
  withLocalDeclD `vampireCnfEquation targetAtom fun equation => do
    some <$> mkLambdaFVars #[equation] (mkApp proof (← mkEqSymm equation))

private partial def transportCnf (body : Expr) (targets : Array Expr)
    (certificate : VampireHammer.Backend.CnfCertificate)
    (formula proof : Expr) (offset : Nat) : MetaM Expr := do
  match ← whnf formula with
  | .app (.app (.const ``Or _) left) right =>
    let leftCase ← withLocalDeclD `vampireCnfLeft left fun hypothesis => do
      mkLambdaFVars #[hypothesis] (← transportCnf body targets certificate left hypothesis offset)
    let rightCase ← withLocalDeclD `vampireCnfRight right fun hypothesis => do
      mkLambdaFVars #[hypothesis]
        (← transportCnf body targets certificate right hypothesis (offset + (← flattenClause left).size))
    pure (mkApp6 (mkConst ``Or.elim) left right body proof leftCase rightCase)
  | .const ``False _ => pure (mkApp2 (mkConst ``False.elim [Level.zero]) body proof)
  | literal =>
    let some index := certificate.permutation.toList.idxOf? offset
      | throwError "CNF certificate omitted a source occurrence"
    let some converted ← certifiedLiteral literal targets[index]! proof
        (certificate.swapped.contains index)
      | throwError "CNF certificate literal changed during transport"
    injectOccurrence body index converted

/-- Replay already-clausal CNF using the certified binder map and occurrence
permutation. No variable-assignment or literal-matching search is performed. -/
def certifiedCnf (parentProof target : Expr) (targetBinders parentBinders : Array String)
    (certificate : VampireHammer.Backend.CnfCertificate) : MetaM (Option Expr) := do
  unless certificate.binders.size == parentBinders.size do return none
  unless parentBinders.toList.eraseDups.length == parentBinders.size &&
      targetBinders.toList.eraseDups.length == targetBinders.size do return none
  for name in parentBinders do
    unless (certificate.binders.filter (·.1 == name)).size == 1 do return none
  for (_, name) in certificate.binders do
    unless targetBinders.contains name do return none
  let rec openTarget (body : Expr) (variables : Array Expr) : MetaM (Option Expr) := do
    if variables.size < targetBinders.size then
      let .forallE name domain inner _ ← whnf body | return none
      withLocalDeclD name domain fun argument => do
        let some proof ← openTarget (inner.instantiate1 argument) (variables.push argument)
          | return none
        some <$> mkLambdaFVars #[argument] proof
    else
      let mut source ← inferType parentProof
      let mut proof := parentProof
      for name in parentBinders do
        let some (_, targetName) := certificate.binders.find? (·.1 == name) | return none
        let some index := targetBinders.toList.idxOf? targetName | return none
        let argument := variables[index]!
        let .forallE _ domain inner _ ← whnf source | return none
        if ← isProp domain then return none
        unless ← isDefEq domain (← inferType argument) do return none
        source := inner.instantiate1 argument
        proof := mkApp proof argument
      let literals ← flattenClause source
      let targets ← flattenClause body
      let permutation := certificate.permutation
      unless literals.size == targets.size && permutation.size == literals.size do return none
      unless permutation.toList.eraseDups.length == permutation.size &&
          permutation.all (· < literals.size) do return none
      unless certificate.swapped.toList.eraseDups.length == certificate.swapped.size &&
          certificate.swapped.all (· < targets.size) do return none
      -- Validate every occurrence even if the resulting clause is unchanged.
      for i in [:targets.size] do
        let literal := literals[permutation[i]!]!
        let valid ← withLocalDeclD `vampireCnfLiteral literal fun hypothesis =>
          certifiedLiteral literal targets[i]! hypothesis (certificate.swapped.contains i)
        if valid.isNone then return none
      if ← isDefEq source body then return some proof
      some <$> transportCnf body targets certificate source proof 0
  let some proof ← openTarget target #[] | return none
  unless ← isDefEq (← inferType proof) target do return none
  pure (some (← mkExpectedTypeHint proof target))

/-- Prove a `cnf_transformation` clause directly from its parent formula; see
the section comment above. -/
def directCnf (parentProof target : Expr) (targetBinders parentBinders : Array String) :
    MetaM (Option Expr) := do
  let rec openTarget (target : Expr) (opened : Array (String × Expr)) :
      MetaM (Option Expr) := do
    if opened.size < targetBinders.size then
      let target ← whnf target
      let .forallE name domain body _ := target | return none
      withLocalDeclD name domain fun opened₀ => do
        let some proof ← openTarget (body.instantiate1 opened₀)
          (opened.push (targetBinders[opened.size]!, opened₀)) | return none
        pure (some (← mkLambdaFVars #[opened₀] proof))
    else
      let variables := opened.map Prod.snd
      let preferred := parentBinders.toList.map fun name =>
        (opened.find? (·.1 == name)).map Prod.snd
      let body := headBetaAll (← instantiateMVars target)
      let result ← proveClause body variables (← inferType parentProof) parentProof preferred
      if result.isNone then
        trace[vampire.replay] "direct CNF failed:\nparent {← inferType parentProof}\nclause {body}"
      pure result
  let some proof ← openTarget target #[] | return none
  unless ← isDefEq (← inferType proof) target do return none
  pure (some (← mkExpectedTypeHint proof target))

/-- Public preprocessing entry point used by the main rule dispatcher.  CNF
searches the cached conjunction leaves; the other rules invoke their VampLean
tactic directly. -/
def reconstruct (input : Input) : MetaM (Option Expr) :=
  Meta.withNewMCtxDepth do
    if input.rule == "cnf_transformation" then
      if let some certificate := input.cnfCertificate? then
        let some proof ← certifiedCnf input.parentProof input.target
            input.targetBinders input.parentBinders certificate
          | throwError "invalid CNF certificate for {input.stepName}"
        trace[vampire.replay] "CNF {input.stepName}: certified clause transport"
        return some proof
      if let some proof ← directCnf input.parentProof input.target
          input.targetBinders input.parentBinders then
        return some proof
      trace[vampire.replay] "CNF {input.stepName}: direct clause extraction failed; using `cnfify`"
      let some candidates ← input.cnfCandidates | do
        trace[vampire.replay] "CNF {input.stepName}: `cnfify` produced no usable clause candidates"
        return none
      -- The candidates and the target mention proof-local Skolem functions
      -- and named predicates symbolically.  Unfolding those lets while
      -- comparing (e.g. a Skolem `Classical.choose` term) is never needed and
      -- can exhaust the heartbeat budget.
      let result ← withConfig (fun config => { config with zetaDelta := false }) <|
        findCnfClause candidates input.target input.targetBinders input.parentBinders
      if result.isNone then
        trace[vampire.replay] "CNF {input.stepName}: no matching clause among {candidates.size} `cnfify` candidate(s)"
      pure result
    else
      runVampLean input

end VampireHammer.BackendPreprocessing

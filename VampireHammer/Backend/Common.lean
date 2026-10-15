import VampireHammer.Backend.Types
import VampireHammer.Clause_Meta

/-!
Shared representation boundaries and clause transports.

`Clause.Holds` stores the ordered regular literals; `AClause.Holds` additionally
stores the AVATAR context with set semantics. Helpers here read those wrappers,
lift regular-clause proofs through the A-clause boundary, and check pointwise
equality orientation. Literal permutations remain an explicit inference.

The `Backend.Internal` namespace is an implementation API for rule modules,
not a second dispatcher. Formula conversion is used at phase and tactic boundaries.
-/

namespace VampireHammer.Backend.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta

/-- The proof-local propositions that Vampire uses as AVATAR split atoms.
Replay supplies them from the decoded symbol kinds; inputs built without
Replay fall back to Vampire's reserved `spl` spelling. -/
def avatarAtoms (input : RuleInput) : Array Expr :=
  input.avatarAtoms?.getD <| input.symbols.toArray.filterMap fun (name, symbol) =>
    if name.startsWith "spl" then some symbol else none

/-- Recognize a positive or negative AVATAR literal without unfolding an
arbitrary proposition. Split symbols are proof-local variables, so expression
identity is the appropriate test here. -/
private def isAvatarLiteral (atoms : Array Expr) (literal : Expr) : Bool :=
  if atoms.any (· == literal) then true
  else
    let literal := literal.consumeMData
    literal.isAppOf ``Not &&
      literal.getAppArgs.any fun argument => atoms.any (· == argument)

/-- Partition a decoded clause while preserving the relative order within its
first-order and AVATAR parts. -/
def splitAClauseLiterals (atoms literals : Array Expr) : Array Expr × Array Expr :=
  literals.foldl (fun (firstOrder, avatar) literal =>
    if isAvatarLiteral atoms literal then
      (firstOrder, avatar.push literal)
    else
      (firstOrder.push literal, avatar)) (#[], #[])

/-- Whether this node should be stored as an A-clause.

`sat_conversion` is the deliberate exit from A-clause form: its result is a
plain propositional `Clause.Holds` consumed by SAT replay or `bv_decide`. Definition nodes
contain `spl` under `↔`, rather than as a clause literal, and therefore remain
ordinary singleton clauses. -/
def storesAClause (input : RuleInput) : Bool :=
  if input.step.inference?.any (fun inference =>
      inference.rule == "sat_conversion" ||
      inference.rule == "avatar_sat_refutation") then
    false
  else
    match input.clauseLiterals? with
    | none => false
    | some literals => literals.any (isAvatarLiteral (avatarAtoms input))

/-- Instantiate the decoded conclusion literal sequence under the binders
opened by `underConclusionBinders`. -/
def targetClauseLiterals? (input : RuleInput) (targetBindings : Array (String × Expr)) :
    Option (Array Expr) :=
  input.clauseLiterals?.map fun literals =>
    literals.map (·.instantiateRev (targetBindings.map Prod.snd))

/-- Definitionally compare literal occurrences in order. Unlike membership or
`List.Perm`, this rejects both a literal-order change and a duplicate change. -/
private def sameLiteralOccurrences (left right : Array Expr) : MetaM Bool := do
  if left.size != right.size then return false
  for index in [:left.size] do
    unless ← isDefEq left[index]! right[index]! do return false
  return true

/-- Transport a regular clause result to the displayed spelling when its
literal occurrence order is unchanged and only equality orientations differ.

Every calculus theorem first constructs its natural clause.  Rather than
teaching each theorem about `a = b` versus `b = a`, its handler can use this
single post-rule bridge.  `ClauseMeta.normalizeEqualityOrientations` verifies
the list length and every position, and builds the corresponding checked
`Clause.map` proof; it never accepts a permutation. -/
def normalizeRegularEqualityResult (proof : Expr) (natural displayed : Array Expr) :
    MetaM (Option Expr) :=
  normalizeEqualityOrientations proof natural.toList displayed.toList

/-- Transport an A-clause across equal AVATAR *sets*.

The regular clause remains an ordered, occurrence-sensitive list. AVATAR
literals, however, are propositional split assumptions: their order is never
addressed by Vampire's inference annotations, and duplicate occurrences have
no logical effect. We retain `List Prop` as the decoded representation, then
certify equality of its memberships in both directions and apply the single
named `AClause.transportAvatarSet` bridge.

Keeping this operation here, rather than in each calculus rule, gives
resolution, subsumption, superposition, and demodulation the same AVATAR-set
contract. -/
def transportAvatarSet (proof : Expr) (regular source target : Array Expr) :
    MetaM (Option Expr) := do
  -- The common case carries the same decoded list verbatim. Preserve that
  -- compact proof term instead of inserting a reflexive set transport.
  if ← sameLiteralOccurrences source target then
    return some proof
  let some sourceInTarget ← containedWitness source.toList target.toList
    | return none
  let some targetInSource ← containedWitness target.toList source.toList
    | return none
  let regularList := mkPropList regular.toList
  let sourceList := mkPropList source.toList
  let targetList := mkPropList target.toList
  some <$> mkAppM ``VampireHammer.Clause.AClause.transportAvatarSet
    #[regularList, sourceList, targetList, sourceInTarget, targetInSource, proof]

/-- Recognize the actual Lean constructor type `Or left right`. `whnf` is used
because a translated proposition can be wrapped in a reducible definition. -/
private def orArguments? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnf type
  match type with
  | .app (.app (.const ``Or _) left) right => pure (some (left, right))
  | _ => pure none

/-- Recognize a negative literal after Lean has unfolded `Not` to `A → False`. -/
def notArgument? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  unless type.isForall do
    return none
  unless ← isProp type.bindingDomain! do
    return none
  unless ← isDefEq type.bindingBody! (mkConst ``False) do
    return none
  pure (some type.bindingDomain!)


/-! ## Clause-list resolution

The TPTP metadata identifies literal *occurrences*, while `Or` is a binary
tree whose association is arbitrary. These helpers read every such tree as an
ordered list and use `Clause.resolve` at Vampire's two reported indices. The
parser boundary is represented by named `Clause.Tree` conversion theorems. A
separate explicit AC inference, rather than a resolution handler, uses
`Clause.reorder` when its displayed clause changes that natural order.
-/

/-- Flatten an arbitrary `Or` tree, retaining duplicate occurrences and the
left-to-right order reported by the TPTP parser. `$false` is the empty clause. -/
partial def flattenClause : Expr → MetaM (Array Expr)
  | formula => do
    let formula ← whnf formula
    if formula.isConstOf ``False then
      return #[]
    match ← orArguments? formula with
    | some (left, right) => return (← flattenClause left) ++ (← flattenClause right)
    | none => return #[formula]

/-- Reify the parser's binary `Or` tree as `Clause.Tree`. Its leaves remain
the original Lean propositions, so `Tree.denote` is definitionally the parsed
formula and `Tree.literals` has the same order as `flattenClause`. -/
partial def clauseTree (formula : Expr) : MetaM Expr := do
  let formula ← whnf formula
  if formula.isConstOf ``False then
    pure (mkConst ``VampireHammer.Clause.Tree.empty)
  else
    match ← orArguments? formula with
    | none => pure (mkAppN (mkConst ``VampireHammer.Clause.Tree.atom) #[formula])
    | some (left, right) =>
      let leftTree ← clauseTree left
      let rightTree ← clauseTree right
      pure (mkAppN (mkConst ``VampireHammer.Clause.Tree.join) #[leftTree, rightTree])

/-- Give a proof a chosen, definitionally equal type. The clause-tree
conversion theorems naturally return expressions such as `tree.denote`; their
types reduce to the original parser formula, but tactics should see that
original formula directly when the reconstructed step becomes a later parent.
An explicitly-instantiated `id` is a zero-cost type ascription in the kernel. -/
def asExpectedType (proof expected : Expr) : MetaM (Option Expr) := do
  unless ← isDefEq (← inferType proof) expected do
    return none
  pure (some (← mkExpectedTypeHint proof expected))

/-- Materialize a clause type from a concrete list of literal propositions. -/
def holdsType (literals : Array Expr) : MetaM Expr := do
  let literalList := mkPropList literals.toList
  pure <| mkApp (mkConst ``VampireHammer.Clause.Holds) literalList

/-- Materialize the proposition type of an A-clause from an ordered regular
literal array and a set-like AVATAR list carrier. -/
private def aClauseType (firstOrder avatar : Array Expr) : MetaM Expr := do
  let firstOrderList := mkPropList firstOrder.toList
  let avatarList := mkPropList avatar.toList
  pure <| mkAppN (mkConst ``VampireHammer.Clause.AClause.Holds)
    #[firstOrderList, avatarList]

/-- Materialize the literal list for a raw parser formula.

For post-CNF proof nodes, `decodedLiterals?` comes from `Replay.decodeSteps`:
it is the clause sequence written by Vampire, translated directly from its
TPTP syntax.  The fallback is only for a raw formula outside that sequential
clause phase. -/
private def formulaClauseType (rawType : Expr)
    (decodedLiterals? : Option (Array Expr) := none) : MetaM Expr := do
  let literals ← match decodedLiterals? with
    | some literals => pure literals
    | none => flattenClause rawType
  holdsType literals

/-- Replace the de Bruijn variables in decoder literals by the local variables
opened from the corresponding leading universal binders. `instantiateRev`
uses the same outer-to-inner binder order as `forallTelescopeReducing`. -/
def instantiateDecodedLiterals (literals : Array Expr) (binders : Array Expr) :
    Array Expr :=
  literals.map (·.instantiateRev binders)

/-- Decode a concrete `List Prop` expression. This small structural reader is
shared by ordinary clauses and by both lists stored in an A-clause. -/
private partial def propListArray? (literals : Expr) (accumulated : Array Expr := #[]) :
    MetaM (Option (Array Expr)) := do
  let literals ← whnf literals
  if literals.isAppOf ``List.nil then return some accumulated
  unless literals.isAppOf ``List.cons do return none
  let arguments := literals.getAppArgs
  if arguments.size < 2 then return none
  let some literal := arguments[arguments.size - 2]? | return none
  let some tail := arguments[arguments.size - 1]? | return none
  propListArray? tail (accumulated.push literal)

/-- Read an already stored clause proof and its literal occurrence list.

Post-CNF parents have type `Clause.Holds literals`; taking the list argument
directly preserves the TPTP clause representation and avoids re-flattening a
canonical `Or` spelling. -/
def clauseView (proof type : Expr) : MetaM (Option (Expr × Array Expr)) := do
  unless type.isAppOf ``VampireHammer.Clause.Holds do
    return none
  let arguments := type.getAppArgs
  if arguments.isEmpty then
    return none
  let some literals := arguments[arguments.size - 1]? | return none
  let some literals ← propListArray? literals | return none
  pure (some (proof, literals))

/-- Put a proof into the clause representation used between replay steps.

The conversion recurses below exactly the leading universal binders recorded
by the parsed TPTP step, because Vampire's unifiers instantiate those binders
before resolution. This count matters: Lean also represents `¬ P` as a
function type, which is a literal rather than a TPTP quantifier. At the body,
a proof that is already a `Holds` proof is retained; otherwise `Tree.toHolds`
performs the one raw-`Or` to clause conversion. The expected `Holds` type is
built from the decoder's literal array when one is available. -/
partial def toClauseForm (proof rawType : Expr) (binderCount : Nat)
    (decodedLiterals? : Option (Array Expr) := none) (asAClause : Bool := false)
    (atoms : Array Expr := #[]) (openedBinders : Array Expr := #[]) :
    MetaM (Option Expr) := do
  let rawType ← whnf rawType
  if binderCount > 0 then
    -- Preserve the named A-clause wrapper. Weak-head reduction would unfold
    -- `AClause.Holds` to an `Or` before this representation boundary can
    -- inspect its two list arguments.
    -- Input proofs can have a reducible local definition as their type.  The
    -- TPTP target is already a visible `∀`, so normalize the proof type too
    -- before deciding whether its matching binder can be opened.
    let proofType ← whnf (← inferType proof)
    let domainsMatch ← if rawType.isForall && proofType.isForall then
      isDefEq rawType.bindingDomain! proofType.bindingDomain!
    else
      pure false
    unless domainsMatch do
      return none
    withLocalDeclD `clauseBinder rawType.bindingDomain! fun binder => do
      let rawBody := rawType.bindingBody!.instantiate1 binder
      let some body ← toClauseForm (mkApp proof binder) rawBody (binderCount - 1)
        decodedLiterals? asAClause atoms (openedBinders.push binder) | return none
      let result ← mkLambdaFVars #[binder] body
      pure (some result)
  else
    let decodedLiterals? := decodedLiterals?.map fun literals =>
      instantiateDecodedLiterals literals openedBinders
    let literals ← match decodedLiterals? with
      | some literals => pure literals
      | none => flattenClause rawType
    let proofType ← whnf (← inferType proof)
    let (firstOrder, avatar) := if asAClause then splitAClauseLiterals atoms literals
      else (literals, #[])
    let expected ← if asAClause then aClauseType firstOrder avatar else holdsType literals
    if ← isDefEq proofType expected then return some proof
    -- The proof as an ordinary `Clause.Holds literals`.
    let ordinaryExpected ← if asAClause then holdsType literals else pure expected
    let isOrdinary ← if asAClause then isDefEq proofType ordinaryExpected else pure false
    let ordinaryProof? ← if isOrdinary then
      pure (some proof)
    else if let some clause ← clauseView proof proofType then
      normalizeEqualityOrientations proof clause.2.toList literals.toList
    else if ← isDefEq proofType rawType then
      unless ← sameLiteralOccurrences (← flattenClause rawType) literals do return none
      let converted ← mkAppM ``VampireHammer.Clause.Tree.toHolds #[← clauseTree rawType, proof]
      -- Tree.literals is constructed from exactly the occurrences checked
      -- above. Comparing its unreduced nested append expression with the
      -- decoded list repeats expensive reduction; state the checked concrete
      -- list directly. The final kernel check still checks the application.
      pure (some (mkExpectedPropHint converted ordinaryExpected))
    else
      pure none
    let some ordinaryProof := ordinaryProof? | return none
    unless asAClause do return some ordinaryProof
    let concatenated := firstOrder ++ avatar
    let some ordered ← reorderAndNormalize ordinaryProof literals.toList concatenated.toList
      | return none
    let firstOrderList := mkPropList firstOrder.toList
    let avatarList := mkPropList avatar.toList
    let converted ← mkAppM ``VampireHammer.Clause.AClause.fromClause
      #[firstOrderList, avatarList, ordered]
    asExpectedType converted expected

/-- Recover the original TPTP formula from a stored clause proof.

This is intentionally used only at the `grind` boundary. Dedicated inference
rules keep their parents and conclusions in `Holds` form, while a fallback
tactic receives ordinary `Or` formulas matching the parsed proof step. -/
partial def fromClauseForm (proof rawType : Expr) (binderCount : Nat)
    (decodedLiterals? : Option (Array Expr) := none) (openedBinders : Array Expr := #[]) :
    MetaM (Option Expr) := do
  let rawType ← whnf rawType
  if binderCount > 0 then
    let proofType ← whnf (← inferType proof)
    unless ← (pure (rawType.isForall && proofType.isForall) <&&>
        isDefEq rawType.bindingDomain! proofType.bindingDomain!) do
      return none
    withLocalDeclD `formulaBinder rawType.bindingDomain! fun binder => do
      let rawBody := rawType.bindingBody!.instantiate1 binder
      let some body ← fromClauseForm (mkApp proof binder) rawBody (binderCount - 1)
        decodedLiterals? (openedBinders.push binder) | return none
      pure (some (← mkLambdaFVars #[binder] body))
  else
    let tree ← clauseTree rawType
    let decodedLiterals? := decodedLiterals?.map fun literals =>
      instantiateDecodedLiterals literals openedBinders
    let literals ← match decodedLiterals? with
      | some literals => pure literals
      | none => flattenClause rawType
    -- Keep `AClause.Holds` opaque long enough to recover its two lists.
    let proofType ← inferType proof
    let ordinaryProof? ← if proofType.isAppOf ``VampireHammer.Clause.AClause.Holds then
      let arguments := proofType.getAppArgs
      if arguments.size < 2 then return none
      let some firstOrderList := arguments[arguments.size - 2]? | return none
      let some avatarList := arguments[arguments.size - 1]? | return none
      let some firstOrder ← propListArray? firstOrderList | return none
      let some avatar ← propListArray? avatarList | return none
      let concatenated := firstOrder ++ avatar
      let converted ← mkAppM ``VampireHammer.Clause.AClause.toClause
        #[firstOrderList, avatarList, proof]
      reorderAndNormalize converted concatenated.toList literals.toList
    else
      let expected ← holdsType literals
      if ← isDefEq proofType expected then pure (some proof) else pure none
    let some ordinaryProof := ordinaryProof? | return none
    unless ← sameLiteralOccurrences (← flattenClause rawType) literals do return none
    -- The tree and concrete list have the same checked occurrences. Avoid
    -- reducing Tree.literals/Tree.denote again in the reverse bridge; the
    -- kernel checks this explicit theorem application at the stated type.
    let converted := mkApp2 (mkConst ``VampireHammer.Clause.Tree.fromHolds) tree ordinaryProof
    pure (some (mkExpectedPropHint converted rawType))

/-- Introduce temporary ordinary-formula versions of all clause parents.

The generated lambdas make each formula hypothesis depend on its checked
clause proof. Thus `grind` sees the syntax it understands, without the replay
DAG ever storing an additional raw proof. -/
partial def withFormulaParents (parents : Array ParentProof) (index : Nat)
    (formulaParents : Array Expr) (k : Array Expr → MetaM Expr) : MetaM Expr := do
  if h : index < parents.size then
    let parent := parents[index]
    if parent.clauseForm then
      let some formulaProof ← fromClauseForm parent.proof parent.target parent.binders.size
        parent.clauseLiterals?
        | throwError "could not recover the parser formula for `grind` parent `{parent.parent.name}`"
      trace[vampire.replay] "grind boundary: converted clause parent {parent.parent.name} to its parser formula"
      let name := (`vampireFormulaParent).appendIndexAfter index
      withLocalDeclD name parent.target fun formulaParent => do
        let body ← withFormulaParents parents (index + 1)
          (formulaParents.push formulaParent) k
        pure <| mkApp (← mkLambdaFVars #[formulaParent] body) formulaProof
    else
      -- Before CNF, the parent already has the parser formula type and can be
      -- used by `grind` without a representation conversion.
      withFormulaParents parents (index + 1) (formulaParents.push parent.proof) k
  else
    k formulaParents

/-- The two literal lists stored by `AClause.Holds`.

`regular` is the clause on which first-order inference rules operate;
`avatar` is propositional context that those rules merely carry along. -/
structure AClauseView where
  proof : Expr
  regular : Array Expr
  avatar : Array Expr

/-- Read an already stored A-clause without converting either half back to an
`Or` expression. -/
def aClauseView (proof type : Expr) : MetaM (Option AClauseView) := do
  -- Do not `whnf` here: `AClause.Holds` is a transparent definition whose
  -- weak-head normal form is an `Or`. The named wrapper is precisely the
  -- representation boundary this reader is meant to recognize.
  unless type.isAppOf ``VampireHammer.Clause.AClause.Holds do return none
  let arguments := type.getAppArgs
  if arguments.size < 2 then return none
  let some regularList := arguments[arguments.size - 2]? | return none
  let some avatarList := arguments[arguments.size - 1]? | return none
  let some regular ← propListArray? regularList | return none
  let some avatar ← propListArray? avatarList | return none
  pure <| some { proof, regular, avatar }

/-- Uniform view used by resolution. Ordinary clauses have an empty AVATAR
half; `isAClause` remembers whether the result must stay in A-clause form. -/
structure ResolutionClauseView where
  proof : Expr
  regular : Array Expr
  avatar : Array Expr
  isAClause : Bool

def resolutionClauseView (proof type : Expr) : MetaM (Option ResolutionClauseView) := do
  if let some aClause ← aClauseView proof type then
    return some {
      proof := aClause.proof, regular := aClause.regular,
      avatar := aClause.avatar, isAClause := true
    }
  if let some clause ← clauseView proof type then
    return some { proof := clause.1, regular := clause.2, avatar := #[], isAClause := false }
  pure none

/-- Orient one selected regular literal through the shared clause bridge.

Every calculus handler keeps its clause order and AVATAR context intact.  The
only permitted change here is equality symmetry at one named regular
occurrence.  Ordinary clauses use `ClauseMeta.orientLiteralAt` directly.  For
an A-clause the same regular-clause transform is lifted with
`AClause.mapFirstOrder`, leaving the AVATAR list literally unchanged.

This is intentionally an occurrence-level API: each inference still decides
which literal it selected, while `Clause_Meta` owns all construction of
`eq_comm` and `ne_comm` proof terms. -/
def orientRegularLiteralAt (view : ResolutionClauseView) (index : Nat)
    (targetLiteral : Expr) : MetaM (Option ResolutionClauseView) := do
  let source := view.regular.toList
  if !view.isAClause then
    let some (proof, oriented) ← orientLiteralAt view.proof source index targetLiteral
      | return none
    return some {
      proof, regular := oriented.toArray, avatar := view.avatar, isAClause := false
    }
  let sourceHolds ← holdsType view.regular
  withLocalDeclD `orientationSource sourceHolds fun regularProof => do
    let some (normalized, oriented) ← orientLiteralAt regularProof source index targetLiteral
      | return none
    let transform ← mkLambdaFVars #[regularProof] normalized
    let sourceList := mkPropList source
    let targetList := mkPropList oriented
    let avatarList := mkPropList view.avatar.toList
    let proof ← mkAppM ``VampireHammer.Clause.AClause.mapFirstOrder
      #[sourceList, targetList, avatarList, transform, view.proof]
    pure <| some {
      proof, regular := oriented.toArray, avatar := view.avatar, isAClause := true
    }

/-- Apply a one-parent first-order inference to the regular half of a clause.

Factoring and the equality simplification rules have one logical parent.  For
an ordinary clause, `build` is used directly.  For an A-clause, it is proved
locally over `Clause.Holds regular` and lifted through `AClause.mapFirstOrder`;
the AVATAR literal set is then transported to the decoded child.  This keeps
every such handler focused on its calculus rule rather than repeating
representation plumbing. -/
def mapRegularInference (view : ResolutionClauseView)
    (targetRegular targetAvatar : Array Expr)
    (build : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  if !view.isAClause then
    if !targetAvatar.isEmpty then return none
    return ← build view.proof
  let sourceType ← holdsType view.regular
  withLocalDeclD `aClauseRegular sourceType fun regularProof => do
    let some transformed ← build regularProof | return none
    let transform ← mkLambdaFVars #[regularProof] transformed
    let sourceList := mkPropList view.regular.toList
    let targetList := mkPropList targetRegular.toList
    let avatarList := mkPropList view.avatar.toList
    let core ← mkAppM ``VampireHammer.Clause.AClause.mapFirstOrder
      #[sourceList, targetList, avatarList, transform, view.proof]
    transportAvatarSet core targetRegular view.avatar targetAvatar

/-- Finish a calculus inference whose natural result is already in clause
form.

The rule-specific theorem determines the regular literal order.  This shared
adapter then accepts only a pointwise equality-orientation change between that
natural regular list and Vampire's displayed list.  For A-clauses it lifts the
same regular bridge through `AClause.mapFirstOrder` and separately transports
the AVATAR context with its set semantics.  It is deliberately the common
post-rule adapter for clause-calculus inferences: no handler should need to
manufacture `eq_comm` or `ne_comm` itself. -/
def normalizeClauseResult (proof : Expr)
    (naturalRegular naturalAvatar targetRegular targetAvatar : Array Expr)
    (isAClause : Bool) : MetaM (Option Expr) := do
  if !isAClause then
    if !naturalAvatar.isEmpty || !targetAvatar.isEmpty then return none
    return ← normalizeRegularEqualityResult proof naturalRegular targetRegular
  let naturalHolds ← holdsType naturalRegular
  withLocalDeclD `naturalRegularProof naturalHolds fun regularProof => do
    let some normalized ← normalizeRegularEqualityResult regularProof
      naturalRegular targetRegular | return none
    let transform ← mkLambdaFVars #[regularProof] normalized
    let naturalRegularList := mkPropList naturalRegular.toList
    let targetRegularList := mkPropList targetRegular.toList
    let naturalAvatarList := mkPropList naturalAvatar.toList
    let mapped ← mkAppM ``VampireHammer.Clause.AClause.mapFirstOrder
      #[naturalRegularList, targetRegularList, naturalAvatarList, transform, proof]
    transportAvatarSet mapped targetRegular naturalAvatar targetAvatar

/-- Create a synthetic-opaque goal for `type` in the current local context
minus `hidden`.  A hidden fvar is kept when another remaining declaration or
`type` depends on it (for example a Skolem `let` whose value mentions a source
fact).  This replaces clearing the hypotheses one by one: every `clear`
rescans the context and allocates a new goal, which is quadratic in the
number of source facts. -/
def mkGoalWithout (type : Expr) (hidden : Array FVarId) : MetaM MVarId := do
  let lctx ← getLCtx
  let hiddenSet : FVarIdSet := hidden.foldl (·.insert ·) {}
  let mut deps := Lean.collectFVars {} (← instantiateMVars type)
  for decl in lctx do
    if decl.isImplementationDetail || hiddenSet.contains decl.fvarId then continue
    deps := Lean.collectFVars deps (← instantiateMVars decl.type)
    if let some value := decl.value? then
      deps := Lean.collectFVars deps (← instantiateMVars value)
  -- A hidden fvar kept for a dependency may itself depend on another one.
  let mut changed := true
  while changed do
    changed := false
    for fvarId in hidden do
      if deps.fvarSet.contains fvarId then
        let before := deps.fvarSet.size
        let decl ← fvarId.getDecl
        deps := Lean.collectFVars deps (← instantiateMVars decl.type)
        if let some value := decl.value? then
          deps := Lean.collectFVars deps (← instantiateMVars value)
        if deps.fvarSet.size != before then changed := true
  let lctx := hidden.foldl (init := lctx) fun lctx fvarId =>
    if deps.fvarSet.contains fvarId then lctx else lctx.erase fvarId
  let goal ← mkFreshExprMVarAt lctx (← getLocalInstances) type .syntheticOpaque
  pure goal.mvarId!

end VampireHammer.Backend.Internal

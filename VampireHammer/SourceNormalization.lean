import VampireHammer.HeterogeneousEquality
import VampireHammer.SubtypeRelativization

open Lean Meta

register_option vampire.autoUnfold : Bool := {
  defValue := true
  descr := "Unfold definitions whose applications require higher-order TF0 arguments"
}

register_option vampire.autoUnfoldLimit : Nat := {
  defValue := 32
  descr := "Maximum automatic definition expansions per source fact"
}
register_option vampire.normalizeProofArguments : Bool := {
  defValue := true
  descr := "Reduce definitionally redundant proof arguments and reflexive equality transports"
}
register_option vampire.unfoldingPlan : Bool := {
  defValue := true
  descr := "Decide once per problem which definitions to unfold and unfold them in every fact \
    (see `VampireHammer.UnfoldingPlan`), instead of within each fact separately"
}
register_option vampire.alignNestedDefinitions : Bool := {
  defValue := true
  descr := "Align logical definitions nested in the goal with the same definitions in selected facts"
}

namespace VampireHammer.SourceNormalization

initialize registerTraceClass `vampire.unfold

/-- Restore the syntax expected by Auto's monomorphizer after adding facts or
unfolding definitions. Reduce lets and beta redexes, and express primitive
structure projections using their named projection functions. All changes are
definitional; ordinary user definitions retain their names. -/
def normalizeSyntax (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  -- Most source facts contain nothing to normalize. These pure scans avoid
  -- the binder-opening traversals of `zetaReduce` and `Meta.transform`.
  let lctx ← getLCtx
  let expression ← if (expression.find? fun e =>
      e.isFVar && (lctx.find? e.fvarId!).any (·.isLet)).isSome then
    zetaReduce expression else pure expression
  unless (expression.find? fun e => e.isMData || e.isLet || e.isProj || e.isHeadBetaTarget).isSome do
    return expression
  let expression ← Core.betaReduce expression
  Meta.transform expression (pre := fun expression => do
    if let .mdata _ body := expression then
      return .visit body
    if let .letE _ _ value body _ := expression then
      return .visit (body.instantiate1 value)
    if expression.isHeadBetaTarget then
      return .visit expression.headBeta
    return .continue (← Auto.unfoldProj expression))

/-- Resolve typeclass operation projections through their actual instances.
This rule uses declaration metadata, not names of mathematical domains. -/
private def exposeHead (expression : Expr) : MetaM Expr := do
  let .const name _ := expression.getAppFn | return expression
  let some info ← getProjectionFnInfo? name | return expression
  unless info.fromClass do return expression
  withTransparency .instances <| whnf expression

/-- Compatibility entry point for domain-independent source syntax reduction.
Definition expansion belongs to the bounded first-order lowering pass. -/
def normalizeType (type : Expr) : MetaM Expr := normalizeSyntax type

-- The user-facing `decide` constant is actually `Decidable.decide`. Resolve
-- its name so Auto's checked rewrite runs before a dependent recursor is exposed.
def logicalHeads : Array Name := #[
  `Eq, `HEq, `And, `Or, `Not, `Iff, `Exists, `True, `False, `ite, `dite, ``decide]

/-- Whether `expression` applies a definition or recursor other than a logical
connective. Only such applications are changed by `normalizeProofArguments`
and `unfoldForFirstOrder`; this pure scan lets both skip the rest. -/
private def hasDefinitionApplication (env : Environment) (expression : Expr) : Bool :=
  (expression.find? fun e => match e.getAppFn with
    | .const name _ => !logicalHeads.contains name && match env.find? name with
      | some (.defnInfo _) | some (.recInfo _) => true
      | _ => false
    | _ => false).isSome

/-- Simplify proof-carrying operations by definitional equality, never by
erasing their arguments. In particular a transport between genuinely different
types must retain its equality proof. Bound the reductions and forbid size growth. -/
def normalizeProofArguments (type : Expr) : MetaM Expr := do
  unless vampire.normalizeProofArguments.get (← getOptions) do return type
  unless hasDefinitionApplication (← getEnv) type do return type
  let budget ← IO.mkRef (32 : Nat)
  Meta.transform type (post := fun expression => do
    let .const name _ := expression.getAppFn | return .done expression
    if logicalHeads.contains name then return .done expression
    match (← getEnv).find? name with
    | some (.defnInfo _) | some (.recInfo _) => pure ()
    | _ => return .done expression
    let remaining ← budget.get
    if remaining == 0 then return .done expression
    unless ← expression.getAppArgs.anyM isProof do return .done expression
    let reduced ← withTransparency .default <| whnf expression
    if reduced == expression then return .done expression
    -- Expanding a proof-bearing definition can expose a large computation or
    -- dependent signature. Keep only reductions that do not grow the term.
    if reduced.sizeWithoutSharing > expression.sizeWithoutSharing then
      return .done expression
    budget.set (remaining - 1)
    return .done reduced)

/-- Rewrites and specialization introduce proof-carrying wrappers after the
initial source normalization too. Restore both invariants at the final
monomorphization boundary; the existing proof checks against the definitionally
equal type. Genuine transports and opaque proof-dependent operations remain. -/
def prepareForMonomorphization (lemmas : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let lemmas ← Auto.rewriteIteCondDecide lemmas
  lemmas.mapM fun lemma => do
    let type ← normalizeSyntax lemma.type
    let type ← normalizeProofArguments type
    return { lemma with type := ← normalizeSyntax type }

/-- Some higher-order definitions expand into quotient lifts or other
operations with proof arguments depending on quantified variables. Such an
expansion makes Auto's abstraction strictly harder. Retain the original
function symbol for the existing higher-order object encoding instead. -/
def hasBoundProofArgument (expression : Expr) (original : LocalContext) : MetaM Bool := do
  let found ← IO.mkRef false
  let _ ← Meta.transform expression (pre := fun expression => do
    if ← found.get then return .done expression
    for argument in expression.getAppArgs do
      if argument.hasAnyFVar (fun id => !original.contains id) then
        if ← isProof argument then
          found.set true
          break
    return .continue expression)
  found.get

/-- Discover logical property definitions occurring anywhere in the goal.
The caller adds definitionally equal copies of existing selected facts; this
does not look up additional theorems. Keep the original interface forms too. -/
def collectLogicalDefinitions (type : Expr) : MetaM (Array Name) := do
  unless vampire.alignNestedDefinitions.get (← getOptions) do return #[]
  -- Applying byContradiction can leave the target behind an assigned mvar.
  -- Traverse its instantiated body rather than treating that mvar as a leaf.
  let type ← instantiateMVars type
  let names ← IO.mkRef (#[] : Array Name)
  let growth ← IO.mkRef (4096 : Nat)
  let _ ← Meta.transform type (pre := fun expression => do
    if (← names.get).size >= 8 then return .done expression
    let .const name _ := expression.getAppFn | return .continue expression
    if logicalHeads.contains name || (← names.get).contains name then return .continue expression
    let some (.defnInfo _) := (← getEnv).find? name | return .continue expression
    unless ← isProp expression do return .continue expression
    let reduced ← withTransparency .default <| whnf expression
    if reduced == expression then return .continue expression
    unless reduced.isForall ||
        (reduced.getAppFn.isConst && logicalHeads.contains reduced.getAppFn.constName!) do
      return .continue expression
    let extra := reduced.sizeWithoutSharing - expression.sizeWithoutSharing
    if extra > (← growth.get) then return .continue expression
    growth.modify (· - extra)
    names.modify (·.push name)
    -- Walk the exposed body only for discovery. The caller retains both the
    -- source proposition and its definitionally justified expanded copy.
    return .continue reduced)
  names.get

/-- An ordinary TF0 symbol cannot consume a function or proposition value.
Universe/type arguments, proofs and instance arguments are handled by
monomorphization. Instance binders can themselves have function types, so
their binder metadata must be checked before reducing the argument's type.
Type families such as `β : α → Sort v` (the codomain of `DFunLike.coe`), but
not predicates `α → Prop`, are type arguments too: unfolding through them would replace the coercion of a
concrete map by its instance's field, while a generic law such as `map_prod`
keeps `DFunLike.coe` and could no longer match. -/
def hasHigherOrderArgument (expression : Expr) : MetaM Bool := do
  let mut functionType ← inferType expression.getAppFn
  for argument in expression.getAppArgs do
    let .forallE _ _ body binder ← whnf functionType | return false
    functionType := body.instantiate1 argument
    if binder == .instImplicit then continue
    let type ← withTransparency .default <| whnf (← inferType argument)
    if type == mkSort .zero then return true
    unless ← isProp type do
      if type.isForall then
        -- A predicate such as `Set α = α → Prop` is a value; a family into
        -- `Sort v` is not.
        let family ← forallTelescopeReducing type fun _ result => do
          let result ← whnf result
          return result.isSort && !result.isProp
        unless family do return true
  return false

private partial def expandFirstOrderHead (budget : IO.Ref (Nat × Nat)) (original : LocalContext)
    (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  let .const name _ := expression.getAppFn | return expression
  if logicalHeads.contains name then return expression
  let .some (.defnInfo _) := (← getEnv).find? name | return expression
  unless ← hasHigherOrderArgument expression do return expression
  let (remaining, growth) ← budget.get
  if remaining == 0 then
    trace[vampire.unfold] "Unfolding limit reached at {name}"
    return expression
  let projection ← exposeHead expression
  let some reduced ← if projection != expression then pure (some projection)
      else unfoldDefinition? expression (ignoreTransparency := true)
    | return expression
  if reduced == expression then return expression
  let extra := reduced.sizeWithoutSharing - expression.sizeWithoutSharing
  if extra > growth then
    trace[vampire.unfold] "Expression-growth limit reached at {name}"
    return expression
  if ← hasBoundProofArgument reduced original then
    trace[vampire.unfold] "Retained {name}: expansion introduces a bound proof argument"
    return expression
  budget.set (remaining - 1, growth - extra)
  trace[vampire.unfold] "Unfolding {name}: higher-order argument blocks TF0"
  expandFirstOrderHead budget original reduced

/-- Expose definitions at a first-order boundary, without unfolding symbols
that already have ordinary first-order arguments. The expansion count and
 total expression growth are bounded independently for each source fact.
Local higher-order symbols, opaque declarations, and genuine higher-order
quantifiers remain unsupported; no axioms or input facts are discarded. -/
def unfoldForFirstOrder (type : Expr) : MetaM Expr := do
  let options ← getOptions
  unless vampire.autoUnfold.get options do return type
  unless hasDefinitionApplication (← getEnv) type do return type
  let budget ← IO.mkRef (vampire.autoUnfoldLimit.get options, 4096)
  let original ← getLCtx
  Meta.transform type (pre := fun expression => do
    return .continue (← expandFirstOrderHead budget original expression))

/-- Normalize source syntax and expose higher-order definition applications.
No mathematical theorem or domain-specific rewrite is built into this pass. -/
def normalizeLemma (lemma : Auto.Lemma) : MetaM Auto.Lemma := do
  let ⟨fact, parameters⟩ := lemma
  let type ← normalizeType fact.type
  let type ← normalizeProofArguments type
  -- With an unfolding plan, the problem-level pass unfolds definitions.
  let type ← if vampire.unfoldingPlan.get (← getOptions) then normalizeSyntax type
    else normalizeSyntax (← unfoldForFirstOrder type)
  let type ← normalizeSyntax (← normalizeProofArguments type)
  let lemma ← HeterogeneousEquality.normalizeLemma ⟨{ fact with type }, parameters⟩
  SubtypeRelativization.relativize lemma

end VampireHammer.SourceNormalization

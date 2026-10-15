import Auto.Tactic
import VampireHammer.Options
import Std.Sync.Mutex
import Lean.Util.ShareCommon

/-! Bounded, process-local storage of closed Lean proofs. No Vampire output
or metavariable states are retained. -/

namespace VampireHammer.ProofCache

open Lean Meta Elab Tactic

initialize registerTraceClass `vampire.cache

private structure Key where
  expressions : Array Expr
  allLocals : Bool
  definitions : Array (Bool × Array Name)
  options : Options
  deriving BEq

private structure Input where
  key : Key
  locals : Array Expr
  arguments : Array Expr
  levels : List Name
  environment : Environment

private structure Entry where
  key : Key
  proof : Expr
  dependencies : Array ConstantInfo

private initialize entries : Std.Mutex (Array Entry) ← Std.Mutex.new #[]

/-- Clear all cached proofs in the current Lean process. -/
def clear : IO Unit := entries.atomically (set (#[] : Array Entry))

private def canonicalNames (levels : List Name) : List Name :=
  (List.range levels.length).map fun i => `_vampire_cache ++ Name.num .anonymous i

private def canonicalLevels (levels : List Name) : List Level :=
  (canonicalNames levels).map .param

private def cacheOptions (options : Options) : CoreM Options := do
  let mut result : Options := {}
  for (name, value) in options do
    unless (`vampire).isPrefixOf name || (`auto).isPrefixOf name do continue
    if name == `vampire.cache || name == `vampire.quiet then continue
    -- An explicitly supplied default is equivalent to an absent setting.
    let declaration? ← try some <$> getOptionDecl name catch _ => pure none
    if let some declaration := declaration? then
      if declaration.defValue == value then continue
    result := result.insert name value
  return result

private def globalExpression (name : Name) (index : Nat) : MetaM Expr := do
  let info ← getConstInfo name
  -- A polymorphic constant's own binders must not accidentally alias a
  -- caller universe with the same spelling (e.g. both called `u`).
  let levels := info.levelParams.mapIdx fun i _ =>
    Level.param (Name.num (Name.num `_vampire_cache_hint index) i)
  return mkConst name levels

/-- Fingerprint identifier premises by their resolved expressions and types,
not their spelling. Complex premise terms bypass caching: elaborating them a
second time could execute a user tactic or introduce fresh auxiliary declarations. -/
private def input? (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord)) :
    TacticM (Option Input) := do
  let hints ← Auto.parseHints hints
  unless hints.lemdbs.isEmpty do return none
  -- Recursive declarations are elaborator bookkeeping, not premises. Their
  -- types also vary when the same subgoal occurs in another theorem.
  let locals ← ((← getLCtx).getFVarIds.map mkFVar).filterM fun argument =>
    return !(← argument.fvarId!.getDecl).isAuxDecl
  let arguments ← locals.filterM fun argument => return !(← argument.fvarId!.getDecl).isLet
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let close (expression : Expr) :=
    mkLambdaFVars locals expression (usedLetOnly := false) (generalizeNondepLet := false)
  let mut expressions := #[← mkForallFVars locals target
    (usedLetOnly := false) (generalizeNondepLet := false)]
  for term in hints.terms do
    unless term.raw.isIdent do return none
    let expression ← if let some declaration := (← getLCtx).findFromUserName? term.raw.getId then
      pure declaration.toExpr
    else
      let name ← resolveGlobalConstNoOverload term.raw
      globalExpression name expressions.size
    expressions := expressions.push (← close expression)
    expressions := expressions.push (← close (← inferType expression))
  let mut definitions := #[]
  for uord in uords do
    let (defeq, identifiers) ← match uord with
      | `(Auto.uord| $unfolds:unfolds) =>
        let `(Auto.unfolds| u[ $[$names],* ]) := unfolds | return none
        pure (false, names)
      | `(Auto.uord| $defeqs:defeqs) =>
        let `(Auto.defeqs| d[ $[$names],* ]) := defeqs | return none
        pure (true, names)
      | _ => return none
    let mut names := #[]
    for identifier in identifiers do
      let name ← resolveGlobalConstNoOverload identifier.raw
      names := names.push name
      let expression ← globalExpression name expressions.size
      expressions := expressions.push expression
      expressions := expressions.push (← inferType expression)
    definitions := definitions.push (defeq, names)
  expressions ← expressions.mapM instantiateMVars
  if expressions.any (fun e => e.hasMVar || e.hasFVar || e.hasLooseBVars) then return none
  let levels := (expressions.foldl collectLevelParams {}).params.toList
  expressions := expressions.map (·.instantiateLevelParams levels (canonicalLevels levels))
  let key : Key := {
    expressions := expressions
    allLocals := hints.lctxhyps
    definitions := definitions
    options := ← cacheOptions (← getOptions)
  }
  return some { key, locals, arguments, levels, environment := ← getEnv }

private def unchanged (saved current : ConstantInfo) : Bool :=
  saved.levelParams == current.levelParams && saved.type == current.type &&
    saved.value? (allowOpaque := true) == current.value? (allowOpaque := true)

private def lookup (input : Input) : TacticM (Option Expr) := do
  let cached ← entries.atomically do
    return (← get).find? (·.key == input.key)
  let some entry := cached | return none
  let environment ← getEnv
  for dependency in entry.dependencies do
    let some current := environment.find? dependency.name | return none
    unless unchanged dependency current do return none
  let canonical := canonicalNames input.levels
  let proof := (mkAppN (entry.proof.instantiateLevelParams canonical (input.levels.map .param))
    input.arguments).headBeta
  let lctx ← instantiateLCtxMVars (← getLCtx)
  -- Kernel-check the entire instantiated proof in the current environment.
  -- An old term is never trusted merely because its cached type matches.
  match Kernel.check environment lctx (ShareCommon.shareCommon proof) with
  | .error _ => return none
  | .ok type =>
    let target ← instantiateMVars (← (← getMainGoal).getType)
    if Kernel.isDefEqGuarded environment lctx type target then
      return some proof
    return none

/-- Proof-producing tactics can add auxiliary theorems during replay. Inline
their values so a fresh elaboration does not need those transient declarations. -/
private partial def inlineAuxiliaries (original : Environment) (proof : Expr)
    (depth : Nat := 0) : MetaM Expr := do
  if depth > 128 then throwError "proof-cache auxiliary expansion limit exceeded"
  Core.transform proof (pre := fun expression => do
    if let .mdata _ body := expression then return .visit body
    let .const name levels := expression | return .continue
    if (original.find? name).isSome then return .continue
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true)
      | throwError "proof cache cannot close auxiliary declaration `{name}`"
    return .done (← inlineAuxiliaries original
      (value.instantiateLevelParams info.levelParams levels) (depth + 1)))

private def insert (input : Input) (proof : Expr) : TacticM Unit := do
  let proof ← instantiateMVars proof
  let proof ← inlineAuxiliaries input.environment proof
  let proof ← mkLambdaFVars input.locals proof
    (usedLetOnly := false) (generalizeNondepLet := false)
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then return
  let levels := (collectLevelParams {} proof).params
  unless levels.all input.levels.contains do return
  let proof := ShareCommon.shareCommon <|
    proof.instantiateLevelParams input.levels (canonicalLevels input.levels)
  match Kernel.check (← getEnv) {} proof with
  | .error _ => return
  | .ok type =>
    unless Kernel.isDefEqGuarded (← getEnv) {} type input.key.expressions[0]! do return
  let mut names := proof.getUsedConstants
  for expression in input.key.expressions do
    names := names ++ expression.getUsedConstants
  let mut dependencies := #[]
  let mut seen : NameSet := {}
  for name in names do
    unless seen.contains name do
      let some info := (← getEnv).find? name | return
      dependencies := dependencies.push info
      seen := seen.insert name
  entries.atomically do
    let retained := (← get).filter (·.key != input.key)
    -- FIFO eviction bounds retention of large proof terms and old environments.
    let retained := if retained.size >= 128 then retained.extract (retained.size - 127) retained.size
      else retained
    set (retained.push { key := input.key, proof, dependencies })

/-- Reuse a kernel-checked closed proof across elaborations with fresh local
IDs. A miss runs the original tactic; only complete successful proofs are stored. -/
def withCache (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord))
    (action : TacticM Unit) : TacticM Unit := withMainContext do
  unless vampire.cache.get (← getOptions) do return ← action
  let saved ← saveState
  let candidate ← try input? hints uords catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    pure none
  saved.restore
  let some input := candidate
    | trace[vampire.cache] "bypass (complex premises or unresolved metavariables)"; return ← action
  let cached ← try lookup input catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    pure none
  if let some proof := cached then
    trace[vampire.cache] "hit"
    (← getMainGoal).assign proof
    replaceMainGoal []
    return
  saved.restore
  trace[vampire.cache] "miss"
  let goal ← getMainGoal
  action
  let completed ← saveState
  try
    goal.withContext do
      if ← goal.isAssigned then
        insert input (← instantiateMVars (mkMVar goal))
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    -- A proof that cannot be closed over its auxiliaries still remains a
    -- valid result of the original tactic; caching is only an optimization.
    pure ()
  finally
    completed.restore

end VampireHammer.ProofCache

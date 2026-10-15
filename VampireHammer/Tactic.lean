import VampireHammer.Export.Pipeline
import VampireHammer.Export.DirectProof
import VampireHammer.GoalDecomposition
import VampireHammer.EmptyDomains
import VampireHammer.UserMessages
import VampireHammer.ProofCache

/-!
The `vampire` and `vampire_export` tactics and their tactic-state boundary.
-/

namespace VampireHammer

open Lean Meta Elab Tactic
open Export.Internal

register_option vampire.plainSliceShare : Nat := {
  defValue := 50
  descr := "Percentage of the search budget for the attempt without library suggestions"
}

register_option vampire.exposeGoalBinders : Bool := {
  defValue := true
  descr := "Expose definitionally hidden universal binders before negating the goal"
}

/-- A `(key := value)` setting for one call of `vampire` or `vampire_export`. -/
syntax vampireSetting := ppSpace atomic("(" ident " := ") term ")"

/-- `vampire` proves the goal with the Vampire theorem prover and replays
Vampire's proof in Lean, so the result is checked by Lean's kernel.

```
vampire                          -- local hypotheses only as needed by lean-auto
vampire [h₁, h₂, Nat.add_comm]   -- facts to give Vampire
vampire [*]                      -- all local hypotheses
vampire [h] (timeout := 20)      -- Vampire time limit in seconds
vampire [h] (unfold := [Set.BijOn, Function.Injective])
```

Settings, in parentheses before or after the fact list:
* `timeout := n`: Vampire's time limit in seconds (`vampire.timeLimit`);
* `strategy := "..."`: an encoded Vampire strategy (`vampire.strategy`);
* `unfold := [c, ...]`: definitions to unfold before translation;
* `defeq := [c, ...]`: constants whose definitional equations are added;
* `key := value` for any other `vampire.key` option, e.g.
  `higherOrder := true` or `disableAvatar := true`. -/
syntax (name := vampireTactic) "vampire" vampireSetting* Auto.hints vampireSetting* : tactic

/-- Export the problem `vampire` would send, without changing or solving the
goal; the text is passed to `vampire.mockScript`. Takes the same facts and
settings as `vampire`. -/
syntax (name := vampireExport) "vampire_export" vampireSetting* Auto.hints vampireSetting* : tactic

/-- Deprecated spelling of `vampire`, with lean-auto's `u[...]`/`d[...]` hints. -/
syntax (name := vampireCapture) "vampire_capture"
  ("(" &"strategy" " := " str ")")? Auto.hints (Auto.uord)* : tactic

/-- Reduce function equality to pointwise equality before entering first-order
logic. Each extensionality step is justified by Lean's `funext`, and its
arguments become ordinary local elements, even when their type can be empty.
Repeated steps also handle curried and dependent function equality. -/
private def introduceFirstOrderGoal (initial : MVarId) (folded : Array Name := #[]) :
    MetaM (Array FVarId × MVarId × Array Name) := do
  let mut goal := initial
  let mut binders := #[]
  let mut exposedDefinitions := #[]
  -- Head unfolding only changes the target when it exposes a binder. This
  -- leaves scalar predicates opaque and introduces actual local witnesses,
  -- rather than assuming that a quantified domain is inhabited.
  for _ in [:32] do
    let (nextGoal, definitions) ← goal.withContext do
      let stated ← instantiateMVars (← goal.getType)
      -- A premise concluding this very head can only match the folded goal.
      if let .const name _ := stated.getAppFn then
        if folded.contains name then return (goal, #[])
      let original ← withTransparency .instances <| whnf stated
      let transparency := if vampire.exposeGoalBinders.get (← getOptions) then
        TransparencyMode.default else TransparencyMode.instances
      let target ← withTransparency transparency <| whnf original
      let mut definitions := #[]
      -- An operation whose instance field is written inline, such as `≤` of
      -- `SimpleGraph`, is opened by instance reduction alone.
      if let .const name _ := stated.getAppFn then
        if original.isForall && !stated.isForall then
          if let some info ← getProjectionFnInfo? name then
            if info.fromClass then definitions := definitions.push name
      if target.isForall && !original.isForall then
        -- Remember the definition chain so source facts using the same
        -- property can also expose its binders. Otherwise the negated body
        -- can become disconnected from an opaque positive hypothesis.
        let mut cursor := original
        for _ in [:32] do
          let .const name _ := cursor.getAppFn | break
          let some (.defnInfo _) := (← getEnv).find? name | break
          let some body ← unfoldDefinition? cursor (ignoreTransparency := true) | break
          definitions := definitions.push name
          cursor ← withTransparency .instances <| whnf body
          if cursor.isForall then break
      let next ← if target.isForall then goal.replaceTargetDefEq target else pure goal
      return (next, definitions)
    goal := nextGoal
    for name in definitions do
      unless exposedDefinitions.contains name do exposedDefinitions := exposedDefinitions.push name
    let (introduced, body) ← goal.intros
    binders := binders ++ introduced
    goal := body
    -- Introducing a literal binder can expose another property definition.
    -- Inspect the resulting head before deciding that preparation is done.
    if !introduced.isEmpty then continue
    let functionEquality ← goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let some (type, _, _) := target.eq? | return false
      if ← isProp type then return false
      return (← whnf type).isForall
    unless functionEquality do return (binders, goal, exposedDefinitions)
    let [pointwise] ← goal.withContext <| goal.apply (← mkConstWithFreshMVarLevels ``funext)
      | throwError "Function extensionality did not produce a single pointwise goal"
    goal := pointwise
  return (binders, goal, exposedDefinitions)

/-- Tell the instantiated-definition alignment which definitions were
unfolded to introduce the goal (`DefinitionAlignment`). -/
private def withGoalDefinitions [MonadWithOptions m] (definitions : Array Name) (action : m α) : m α :=
  withOptions (fun options => options.set `vampire.goalDefinitions
    (" ".intercalate (definitions.map toString).toList)) action

/-- Keep the conclusion heads of explicit premises folded in the unfolding plan. -/
private def withFoldedDefinitions [MonadWithOptions m] (definitions : Array Name) (action : m α) : m α :=
  withOptions (fun options => options.set `vampire.foldedDefinitions
    (" ".intercalate (definitions.map toString).toList)) action

/-- Heads of the conclusions of explicit premise constants that are named
definitions, such as `Presheaf.IsSheaf` for
`isSheaf_comp_of_isSheaf : … → IsSheaf J (P ⋙ F)`. Introducing the goal keeps
these heads folded. -/
private def premiseConclusions (hints : TSyntax ``Auto.hints) : TacticM (Array Name) := do
  let `(Auto.hints| [ $[$elems],* ]) := hints | return #[]
  let mut heads := #[]
  for elem in elems do
    let `(Auto.hintelem| $term:term) := elem | continue
    unless term.raw.isIdent do continue
    let some name ← (try some <$> resolveGlobalConstNoOverload term.raw catch _ => pure none)
      | continue
    let some info := (← getEnv).find? name | continue
    unless ← isProp info.type do continue
    let head ← forallTelescope info.type fun _ body => pure body.getAppFn
    if let .const head _ := head then
      -- Only named definitions such as `IsSheaf`. Opening a class operation
      -- (`⊆`, `≤`) introduces local elements, which can be the only evidence
      -- that a domain is inhabited; `DefinitionAlignment` reconciles it with
      -- folded premises instead.
      if (← getProjectionFnInfo? head).isSome then continue
      unless heads.contains head do heads := heads.push head
  return heads

/-- Run an action in the refutation context shared by capture and export.
The caller decides whether to assign the contradiction or restore the state. -/
private def withRefutationGoal (folded : Array Name)
    (action : Array FVarId → FVarId → MVarId → Array Name → TacticM α) :
    TacticM α := withMainContext do
  let (binders, goal, definitions) ← introduceFirstOrderGoal (← getMainGoal) folded
  let [negGoal] ← goal.apply (mkConst ``Classical.byContradiction)
    | throwError "Could not create a refutation goal"
  let (negHyp, absurd) ← negGoal.intro1
  replaceMainGoal [absurd]
  withMainContext <| action binders negHyp absurd definitions

/-- lean-auto abstracts the universe metavariables of an elaborated hint into
level parameters `_abstMVar.N`. Monomorphization instantiates them where a
match constrains them; an unconstrained one stays in the instance's proof and
is undeclared for the kernel. The proof is parametric in it, so any level is
valid: use `0`. -/
private def instantiateAbstractedLevels (proof : Expr) : Expr :=
  let params := (collectLevelParams {} proof).params.toList.filter
    (·.getPrefix == `_abstMVar)
  proof.instantiateLevelParams params (params.map fun _ => Level.zero)

/-- Collect the requested facts and assign the replayed contradiction. -/
private def replayGoal (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord))
    (searchBudget? : Option (IO.Ref Nat) := none) (extraBinders : Array FVarId := #[])
    (extraDefinitions : Array Name := #[]) (deferMonoFallback : Bool := false)
    (monoBudget? : Option (IO.Ref Nat) := none) :
    TacticM Unit := do
  let folded ← premiseConclusions hints
  withFoldedDefinitions folded <| withRefutationGoal folded fun binders negHyp absurd definitions => do
    let definitions := (definitions ++ extraDefinitions).foldl
      (fun names name => if names.contains name then names else names.push name) #[]
    let (lemmas, inhs) ← collectFactsWithTypeclassLaws hints uords
      (extraBinders ++ binders) negHyp definitions
    let negType ← negHyp.getType
    let .app (.const ``Not _) target := negType
      | throwError "The refutation hypothesis is not a negation"
    if vampire.directProof.get (← getOptions) then
      if let some direct ← proveWithoutTranslation? target lemmas then
        absurd.assign (mkApp (mkFVar negHyp) direct)
        return
    let proof ← withGoalDefinitions definitions <|
      replayVampireWithAuto lemmas inhs searchBudget? deferMonoFallback monoBudget?
    let proof ← instantiateMVars proof
    if proof.hasExprMVar || proof.hasLevelMVar then
      throwError "Vampire replay left unresolved metavariables"
    absurd.assign (instantiateAbstractedLevels proof)

/-- Obtain the same selected facts as the refutation path for optional goal
preparation. The temporary negative hypothesis guides the existing indexes;
every fact depending on it is removed before simplification or direct proof. -/
private def preparationFacts (hints : TSyntax ``Auto.hints)
    (uords : Array (TSyntax `Auto.uord)) (binders : Array FVarId)
    (definitions : Array Name) : TacticM (Array Auto.Lemma) := withMainContext do
  let target ← (← getMainGoal).getType
  withLocalDeclD `vampirePreparationNegative (mkApp (mkConst ``Not) target) fun negative => do
    let (facts, _) ← collectFactsWithTypeclassLaws hints uords binders negative.fvarId! definitions
    return facts.filter fun fact =>
      !fact.proof.containsFVar negative.fvarId! && !fact.type.containsFVar negative.fvarId!

/-- Run `attempt` on the main goal; if it fails for want of an inhabitant,
prove the goal under `Nonempty` of each local type variable without one, and
defer the nonemptiness proof only where the proof uses it (see `EmptyDomains`). -/
private partial def withDeferredWitness (attempt : TacticM Unit) (budget : IO.Ref Nat)
    (depth : Nat := 8) (emptyBudget? : Option Export.SearchAllowance := none)
    (emptyTypes : Array Expr := #[]) : TacticM Unit := do
  let emptyBudget ← match emptyBudget? with
    | some budget => pure budget
    | none => liftM <| Export.SearchAllowance.create 4000
  let saved ← saveState
  try attempt catch error =>
    let message ← error.toMessageData.toString
    unless depth > 0 && vampire.deferInhabitants.get (← getOptions) &&
        (message.splitOn "no known inhabitation evidence").length > 1 do
      throw error
    saved.restore
    let goal ← getMainGoal
    let types ← goal.withContext <| EmptyDomains.missingCandidates error.toMessageData
    Export.diagnosticEvent "missing_domain" [("error", toJson message),
      ("types", toJson (← goal.withContext (types.mapM fun type => return (← ppExpr type).pretty)))]
    if types.isEmpty then throw error
    -- Re-exporting an unchanged empty domain cannot make progress. Avoid
    -- repeatedly assuming an inhabitant already known impossible on this
    -- branch, rerunning preprocessing and consuming the caller's heartbeats.
    if types.size == 1 && emptyTypes.contains types[0]! then
      Export.diagnosticEvent "empty_domain_still_required" []
      throw error
    try
      if types.size == 1 then
        if let some result ← goal.withContext <| EmptyDomains.simplifyKnownEmpty? goal types[0]! (some emptyBudget) then
          Export.diagnosticEvent "known_empty_domain" []
          match result with
          | none => setGoals []; return
          | some inner =>
            setGoals [inner]
            withDeferredWitness attempt budget (depth - 1) (some emptyBudget) (emptyTypes ++ types)
            return
      -- Targeted recovery can discover another missing sort on the next
      -- attempt. Each assumption and empty branch still requires a proof.
      let mut chain := #[]
      let mut current := goal
      for type in types do
        let (inner, assumed) ← EmptyDomains.assume current type
        chain := chain.push (current, type, assumed)
        current := inner
      Export.diagnosticEvent "assuming_nonempty" []
      setGoals [current]
      withDeferredWitness attempt budget (depth - 1) (some emptyBudget) emptyTypes
      -- Discharge from the innermost assumption outwards.
      for (outer, type, assumed) in chain.reverse do
        if let some empty ← EmptyDomains.discharge outer type assumed (some emptyBudget) then
          Export.diagnosticEvent "empty_branch" []
          setGoals [empty]
          withDeferredWitness attempt budget (depth - 1) (some emptyBudget) (emptyTypes.push type)
      setGoals []
      Export.diagnosticEvent "domain_assumptions_discharged" []
    catch deferredError =>
      trace[vampire] "Assuming inhabitants failed: {deferredError.toMessageData}"
      Export.diagnosticEvent "deferred_witness_failed" [
        ("initial_error", toJson message),
        ("terminal_error", toJson (← deferredError.toMessageData.toString))]
      saved.restore
      throw deferredError

/-- Try a small constructor tree with selected simplification and one ext step
per branch after the original attempt. All searches share one
budget. A failed preparation restores the entire tactic/metavariable state. -/
private def tryDecomposedGoal (hints : TSyntax ``Auto.hints)
    (uords : Array (TSyntax `Auto.uord)) (budget : IO.Ref Nat)
    (constructorsOnly : Bool := false) (monoBudget? : Option (IO.Ref Nat) := none) :
    TacticM Bool := withMainContext do
  let options ← getOptions
  unless vampire.decomposeGoals.get options do return false
  let limit := min 8 (vampire.decompositionGoalLimit.get options)
  if limit == 0 then return false
  let originalContext ← getLCtx
  let folded ← premiseConclusions hints
  let saved ← saveState
  try
    let (binders, goal, definitions) ← introduceFirstOrderGoal (← getMainGoal) folded
    replaceMainGoal [goal]
    unless ← GoalDecomposition.isCandidate goal do
      saved.restore
      return false
    let facts ← preparationFacts hints uords binders definitions
    if let some proof ← proveWithoutTranslation? (← goal.getType) facts then
      goal.assign proof
      replaceMainGoal []
      return true
    let excluded ← Term.getDeclName?
    let (branches, extended) ← match ← GoalDecomposition.split? goal limit with
      | some branches => pure (branches, false)
      | none =>
        if constructorsOnly then saved.restore; return false
        let some branches ← GoalDecomposition.extensionality? goal limit excluded
          | saved.restore; return false
        pure (branches, true)
    let mut pending := branches.map fun branch => (branch, 1, extended, definitions)
    let mut generated := branches.size
    let mut leaf := 0
    let destination := vampire.outputPath.get options
    while !pending.isEmpty do
      let (branch, depth, extended, inheritedDefinitions) := pending[0]!
      pending := pending.extract 1 pending.size
      replaceMainGoal [branch]
      let (children, usedLeaf) ← withMainContext do
        let (_, prepared, opened) ← introduceFirstOrderGoal branch folded
        replaceMainGoal [prepared]
        withMainContext do
          let definitions := (inheritedDefinitions ++ opened).foldl
            (fun names name => if names.contains name then names else names.push name) #[]
          let allowed := (← getLCtx).getFVarIds.filter (fun id => !originalContext.contains id)
          let facts ← preparationFacts hints uords allowed definitions
          if let some proof ← proveWithoutTranslation? (← prepared.getType) facts then
            prepared.assign proof
            return (#[], false)
          else if let some simplified ← GoalDecomposition.simplify prepared facts then
            replaceMainGoal [simplified]
            let available := limit - generated
            let split ← if depth < 2 then GoalDecomposition.split? simplified available else pure none
            if let some children := split then
              return (children.map (fun child => (child, depth + 1, extended, definitions)), false)
            else if let some children ← if !constructorsOnly && !extended then
                GoalDecomposition.extensionality? simplified available excluded else pure none then
              return (children.map (fun child => (child, depth, true, definitions)), false)
            else
              let path := if destination.isEmpty then "" else destination ++ s!".branch-{leaf}.p"
              withOptions (fun options => options.set `vampire.outputPath path) <|
                withDeferredWitness (budget := budget)
                  (replayGoal hints uords (some budget) allowed definitions constructorsOnly monoBudget?)
              return (#[], true)
          else
            return (#[], false)
      generated := generated + children.size
      pending := pending ++ children
      if usedLeaf then leaf := leaf + 1
    replaceMainGoal []
    return true
  catch error =>
    saved.restore
    if error.isInterrupt || error.isRuntime then throw error
    trace[vampire] "Structural goal preparation declined: {error.toMessageData}"
    return false

/-- On the sliced/default FO route, try a shallow constructor tree before the
native HO retry when monomorphization exhausts its local window. All branch
monomorphizations share one additional window; no branch starts an HO retry. -/
private def replayGoalWithMonoDecomposition (hints : TSyntax ``Auto.hints)
    (uords : Array (TSyntax `Auto.uord)) (budget : IO.Ref Nat)
    (monoDecomposed : IO.Ref Bool) : TacticM Unit := do
  monoDecomposed.set false
  let options ← getOptions
  unless vampire.monoHeartbeats.get options > 0 && !vampire.higherOrder.get options &&
      !InternalSearch.staged options && !vampire.routedSlices.get options &&
      !InternalSearch.routed options && vampire.decomposeGoals.get options &&
      vampire.monoDecomposition.get options do
    return ← replayGoal hints uords (some budget)
  let saved ← saveState
  try
    replayGoal hints uords (some budget) #[] #[] true
  catch error =>
    unless isMonoDeadline (← error.toMessageData.toString) do throw error
    saved.restore
    monoDecomposed.set true
    let monoBudget ← IO.mkRef (vampire.monoHeartbeats.get options * 1000)
    if ← tryDecomposedGoal hints uords budget true (some monoBudget) then return
    -- Preparation restored the original goal. Retry it directly in HO rather
    -- than spending another FO window or allowing an HO-to-FO retry.
    if vampire.timeLimit.get options != 0 && (← budget.get) < 1000 then throw error
    preserveBeforeMonoHigherOrder
    withOptions (fun options => options.set `vampire.higherOrder true
      |>.set `vampire.higherOrderFallback false |>.set `vampire.strategy ""
      |>.set `auto.mono.saturationThreshold 0) <|
      replayGoal hints uords (some budget)

/-- Library suggestions enlarge the problem and can slow down a search that
succeeds without them. Search the plain problem first, with a bounded share
of the budget, then the enlarged problem with the rest. -/
private def replaySlices (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord))
    (budget : IO.Ref Nat) (monoDecomposed : IO.Ref Bool) : TacticM Unit := do
  let options ← getOptions
  let total ← budget.get
  if vampire.suggestedLemmas.get options == 0 || total == 0 then
    return ← replayGoalWithMonoDecomposition hints uords budget monoDecomposed
  if vampire.plainSliceShare.get options == 0 then
    return ← replayGoalWithMonoDecomposition hints uords budget monoDecomposed
  let allotted := total * vampire.plainSliceShare.get options / 100
  let share ← IO.mkRef allotted
  let saved ← saveState
  try
    withOptions (·.set `vampire.suggestedLemmas 0) <|
      replayGoalWithMonoDecomposition hints uords share monoDecomposed
  catch plainError =>
    budget.modify (· - (allotted - min allotted (← share.get)))
    saved.restore
    trace[vampire] "Plain slice failed; retrying with library suggestions: {plainError.toMessageData}"
    replayGoalWithMonoDecomposition hints uords budget monoDecomposed

/-- Whether the goal, after its first-order introduction, is one that
`tryDecomposedGoal` can split. Observational: the state is restored. -/
private def decomposesGoal (hints : TSyntax ``Auto.hints) : TacticM Bool := do
  unless vampire.decomposeGoals.get (← getOptions) && vampire.decompositionGoalLimit.get (← getOptions) > 0 do
    return false
  let saved ← saveState
  try
    withMainContext do
      let folded ← premiseConclusions hints
      let (_, goal, _) ← introduceFirstOrderGoal (← getMainGoal) folded
      GoalDecomposition.isCandidate goal
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    pure false
  finally
    saved.restore

private def captureGoal (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord)) :
    TacticM Unit := do
  if vampire.parallel.get (← getOptions) then
    let tacticContext ← read
    let tacticState ← get
    let termContext ← readThe Term.Context
    let termState ← getThe Term.State
    let main : TacticM Unit := do
      let budget ← IO.mkRef (vampire.timeLimit.get (← getOptions) * 1000)
      withFoldedDefinitions (← premiseConclusions hints) <|
        withDeferredWitness (replayGoal hints uords (some budget)) budget
    let split : TacticM Unit := do
      let budget ← IO.mkRef (vampire.timeLimit.get (← getOptions) * 1000)
      let destination := vampire.outputPath.get (← getOptions)
      withOptions (fun options => options.set `vampire.outputPath
          (if destination.isEmpty then "" else destination ++ ".split")) do
        unless ← tryDecomposedGoal hints uords budget do
          throwError "Parallel goal decomposition did not close the goal"
    let actions := if ← decomposesGoal hints then #[main, split] else #[main]
    let workers := actions.map fun action =>
      ((action tacticContext).run tacticState).run termContext termState
    let ((_, tacticState), termState) ← raceMeta workers
    set tacticState
    set termState
    return
  let budget ← IO.mkRef (vampire.timeLimit.get (← getOptions) * 1000)
  let monoDecomposed ← IO.mkRef false
  let run : TacticM Unit :=
    withFoldedDefinitions (← premiseConclusions hints) <| withDeferredWitness (budget := budget) do
      let saved ← saveState
      -- A time-sliced search can use the whole budget before the decomposition
      -- of a splittable goal gets to run, although the decomposition is often
      -- what proves it. Reserve a share for it, returned if unspent.
      let options ← getOptions
      let remaining ← budget.get
      let reserve ← if vampire.routedSlices.get options && (← decomposesGoal hints) then
        pure (remaining * vampire.decompositionReserve.get options / 100) else pure 0
      let main ← IO.mkRef (remaining - reserve)
      try
        replaySlices hints uords (if reserve == 0 then budget else main) monoDecomposed
      catch originalError =>
        saved.restore
        if reserve > 0 then
          budget.set (reserve + (← main.get))
          Export.diagnosticEvent "decomposition_reserve" [("reserve_ms", toJson reserve),
            ("available_ms", toJson (← budget.get))]
        if ← monoDecomposed.get then throw originalError
        unless ← tryDecomposedGoal hints uords budget do
          throw originalError
  let options ← getOptions
  if vampire.routedSlices.get options && vampire.sliceHoFirst.get options > 0 then
    let saved ← saveState
    try run catch error =>
      -- The native slice failed for want of a domain that the inhabitant recovery
      -- could not supply. The first-order slice does not need it: search the time
      -- left with first-order only rather than failing the goal.
      if error.isInterrupt || error.isRuntime then throw error
      let message ← error.toMessageData.toString
      unless (message.splitOn "no known inhabitation evidence").length > 1 do throw error
      saved.restore
      Export.diagnosticEvent "first_order_after_domain_failure" []
      withOptions (·.set `vampire.sliceHoFirst 0) run
  else run

/-- Run the same preprocessing and export path as `vampire`, but pass
the generated text to the configured mock script instead of invoking Vampire.
The saved tactic state makes this an observational export command. -/
private def exportGoal (hints : TSyntax ``Auto.hints) (uords : Array (TSyntax `Auto.uord)) :
    TacticM Unit := do
  let saved ← saveState
  let query ← try
    let folded ← premiseConclusions hints
    withFoldedDefinitions folded <| withRefutationGoal folded fun binders negHyp _ definitions => do
      let (lemmas, inhs) ← collectFactsWithTypeclassLaws hints uords binders negHyp definitions
      withGoalDefinitions definitions <| exportProblem lemmas inhs
  finally
    saved.restore
  captureProblem query

/-- Resolve `vampire`'s settings into option updates and lean-auto hints. -/
private def interpretSettings (settings : Array (TSyntax ``vampireSetting)) :
    TacticM (Array (Name × DataValue) × Array (TSyntax `Auto.uord)) := do
  let mut options := #[]
  let mut uords := #[]
  for setting in settings do
    let `(vampireSetting| ($key := $value)) := setting | throwUnsupportedSyntax
    let identifiers : Unit → TacticM (Array Ident) := fun _ => do
      let `([$names,*]) := value
        | throwErrorAt value "expected a list of constant names, e.g. `[Set.BijOn]`"
      names.getElems.mapM fun name => do
        unless name.raw.isIdent do throwErrorAt name "expected a constant name"
        pure (⟨name.raw⟩ : Ident)
    match key.getId with
    | `unfold => uords := uords.push (← `(Auto.uord| u[$(← identifiers ()),*]))
    | `defeq => uords := uords.push (← `(Auto.uord| d[$(← identifiers ()),*]))
    | name =>
      let name := if name == `timeout then `timeLimit else name
      let option := `vampire ++ name
      let decl ← try getOptionDecl option catch _ =>
        throwErrorAt key "unknown setting `{key.getId}`; expected `timeout`, `strategy`, \
          `unfold`, `defeq`, or the name of a `vampire.*` option"
      let data ← match decl.defValue, value.raw.isNatLit?, value.raw.isStrLit? with
        | .ofNat _, some n, _ => pure (DataValue.ofNat n)
        | .ofString _, _, some text => pure (DataValue.ofString text)
        | .ofBool _, _, _ =>
          match value.raw.isIdent, value.raw.getId with
          | true, `true => pure (DataValue.ofBool true)
          | true, `false => pure (DataValue.ofBool false)
          | _, _ => throwErrorAt value "expected `true` or `false`"
        | .ofNat _, _, _ => throwErrorAt value "expected a natural number"
        | .ofString _, _, _ => throwErrorAt value "expected a string literal"
        | _, _, _ => throwErrorAt key "setting `{key.getId}` cannot be set here"
      options := options.push (option, data)
  return (options, uords)

private def withSettings (settings : Array (TSyntax ``vampireSetting))
    (run : Array (TSyntax `Auto.uord) → TacticM Unit) : TacticM Unit := do
  let (options, uords) ← interpretSettings settings
  withOptions (fun opts => options.foldl (fun opts (name, value) => opts.insert name value) opts)
    (run uords)

/-- Reject invalid budgets before collecting facts or invoking the prover. -/
private def validateOptions : TacticM Unit := do
  let options ← getOptions
  for name in #[`vampire.plainSliceShare, `vampire.higherOrderSliceShare,
      `vampire.sliceHoFirst, `vampire.sliceFo, `vampire.sliceFoBeforeRecovery,
      `vampire.decompositionReserve] do
    let .ofNat defaultValue := (← getOptionDecl name).defValue | unreachable!
    let value : Nat := options.get name defaultValue
    if value > 100 then
      throwError "`{name}` must be a percentage between 0 and 100; got {value}."
  if vampire.sliceHoFirst.get options + vampire.sliceFo.get options > 100 then
    throwError "`vampire.sliceHoFirst` and `vampire.sliceFo` must total at most 100%."
  if vampire.timeLimit.get options == 0 then
    if vampire.routedSlices.get options && !vampire.parallel.get options then
      throwError "`vampire.routedSlices` needs a positive timeout; use `(timeout := 10)`. For unlimited search, also set `(routedSlices := false)`."

/-- Children of `vampire`/`vampire_export`: settings, facts, settings. The
trailing repetition after the optional fact list cannot be matched by a
quotation pattern, so the node is read positionally. -/
private def callParts (stx : Syntax) :
    Array (TSyntax ``vampireSetting) × TSyntax ``Auto.hints :=
  ((stx[1].getArgs ++ stx[3].getArgs).map (⟨·⟩), ⟨stx[2]⟩)

@[tactic vampireTactic] def evalVampire : Tactic := fun stx => do
  let (settings, hints) := callParts stx
  withSettings settings fun uords => do
    validateOptions
    UserMessages.withFailureHint <| ProofCache.withCache hints uords (captureGoal hints uords)
    unless vampire.quiet.get (← getOptions) do
      logInfo "vampire closed the goal."

@[tactic vampireExport] def evalVampireExport : Tactic := fun stx => do
  let (settings, hints) := callParts stx
  withSettings settings (exportGoal hints)

elab_rules : tactic
  | `(vampireCapture| vampire_capture $[(strategy := $strategy)]? $hints $[$uords]*) => do
    logWarning "`vampire_capture` is deprecated; use `vampire` \
      (`(strategy := ...)` and `(unfold := [...])` are settings of `vampire`)"
    match strategy with
    | some strategy =>
      withOptions (fun opts => opts.set `vampire.strategy strategy.getString) do
        ProofCache.withCache hints uords (captureGoal hints uords)
    | none => ProofCache.withCache hints uords (captureGoal hints uords)

end VampireHammer

import VampireHammer.SourceNormalization
import VampireHammer.AttributeLemmas
import Lean.Meta.Tactic.LibrarySearch

/-!
# Sibling lemma discovery

The attribute collector consults the `simp` and `grind` indexes, but the facts
missing from hard problems are frequently plain environment theorems that no
attribute indexes: the `Set.mem_dite_univ_left` behind a stuck `Set.mem_ite_univ_left`
goal, or the Int-specific `Int.mul_eq_zero` behind the generic `MulZeroClass` law.

This collector retrieves such siblings semantically. Query terms are the
proposition-shaped applications occurring in the source problem, including
equality and order statements that attribute anchors deliberately skip, and each
query is enriched by bounded definitional variants: one-step unfoldings of
constant-headed arguments, a bridge from `ite` arguments to the `dite` forms
sibling statements are phrased over, and pointwise instances of function
equalities. Retrieval uses the library-search discrimination tree maintained by
Lean core (the `exact?` index over all imported declarations, built in parallel
at import time); acceptance still requires a definitional match of the
candidate statement at reducible transparency with a bounded fallback to default
transparency, universal closure of leftover parameters and no datatype theories
beyond those of the source problem. Query metavariables are generalized to
universally quantified variables in the selected fact, so acceptance is
deterministic for polymorphic goals. Selected facts are ordinary theorem
references, so the checked replay path is the same as for requested facts.

The collection runs inside its own bounded heartbeat window: a deterministic
timeout inside it would otherwise abort the enclosing command and lose the whole
case, and an unbounded search would starve the export, the search and the
replay of the enclosing command's budget. Since the core exception instance
rethrows runtime exceptions, every phase is contained with `tryCatchRuntimeEx`,
and the lazily built library-search index is warmed once per process in its own
window before the bounded loop. Cases with little budget left skip sibling
selection entirely, so no case can lose a proof to it.
-/

open Lean Meta

register_option vampire.siblingLemmas : Bool := {
  defValue := false
  descr := "Select plain environment theorems whose statements mention propositions of the source problem"
}
register_option vampire.siblingLemmaLimit : Nat := {
  defValue := 16
  descr := "Maximum automatically selected sibling theorem instances"
}

namespace VampireHammer.SiblingLemmas

def labelPrefix := "sibling lemma "

/-- Heartbeat budget for one sibling collection. One unit is one heartbeat as
counted by `IO.getNumHeartbeats`; the default command budget is 200 million. -/
private def siblingBudget : Nat := 20_000_000

/-- Heartbeat budget for the one-time index warmup. The library-search import
tree is built lazily by the first retrieval of a process, at about twelve
million heartbeats over Mathlib, far beyond one attempt window. -/
private def warmupBudget : Nat := 32_000_000

/-- Skip sibling selection when the enclosing command has fewer than this many
heartbeats left: the export, the search and the replay still need their budget,
and burning even the collection window could push the case over. -/
private def headroomFloor : Nat := 40_000_000

/-- Heartbeat budget for one query traversal, retrieval or specialization.
Nested windows compose: the innermost limit fires first, and the enclosing
collection window still bounds the total burn. -/
private def attemptBudget : Nat := 2_000_000

/-- Run `x` with a fresh heartbeat budget of `budget` heartbeats. Deterministic
timeout checks compare the elapsed count against `initHeartbeats` and
`maxHeartbeats` of the core context, so resetting both gives the enclosed
operations a window of their own: they throw after burning at most `budget`
heartbeats instead of the enclosing command's whole budget. -/
def withHeartbeatBudget {α : Type} (budget : Nat) (x : MetaM α) : MetaM α := do
  let heartbeats ← IO.getNumHeartbeats
  let context ← readThe Core.Context
  let remaining := context.maxHeartbeats - (heartbeats - context.initHeartbeats)
  let allowance := if context.maxHeartbeats == 0 then budget else
    max 1 (if budget == 0 then remaining else min budget remaining)
  withTheReader Core.Context
    (fun ctx => { ctx with initHeartbeats := heartbeats, maxHeartbeats := allowance }) do
      let result ← x
      Core.checkSystem "premise selection"
      return result

/-- Local search failures are optional; cancellation and the caller's deadline
still terminate the tactic. -/
def checkOptionalFailure (error : Exception) : MetaM Unit := do
  Core.checkInterrupted
  Core.checkMaxHeartbeats "premise selection"
  if error.isInterrupt || (error.isRuntime && !error.isMaxHeartbeat) then throw error

/-- One bounded and fully contained attempt. `try`/`catch` deliberately does
not catch the deterministic timeout that a blown window throws — the core
`MonadExcept` instance rethrows runtime exceptions — so `tryCatchRuntimeEx` is
what keeps a failed attempt survivable for the enclosing case. -/
def attempt {α : Type} (budget : Nat) (x : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (do
      let result ← withHeartbeatBudget budget x
      pure (some result))
    (fun error => do
      checkOptionalFailure error
      pure none)

/-- Collect the bounded set of proposition-shaped query terms from one source
expression. Unlike attribute anchors, equality and logical connectives are
retained: sibling statements usually phrase their content through them, and the
library-search tree indexes those shapes. Binder positions become metavariables,
as in attribute anchoring. -/
private partial def queries (e : Expr) (result : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut result := result
  if result.size >= 32 then return result
  if !e.hasLooseBVars && e.isApp then
    if let .const head _ := e.getAppFn then
      if head != ``True && head != ``False then
        if ← isProp e then
          unless result.contains e do result := result.push e
  match e with
  | .app .. =>
    for argument in e.getAppArgs do
      if result.size >= 32 then break
      let type ← inferType argument
      if type.isSort && type != mkSort .zero then continue
      result ← queries argument result
    return result
  | .forallE _ t b _ | .lam _ t b _ =>
    result ← queries t result
    let argument ← mkFreshExprMVar t
    queries (b.instantiate1 argument) result
  | .letE _ t v b _ => queries (b.instantiate1 v) (← queries v (← queries t result))
  | .mdata _ b | .proj _ _ b => queries b result
  | _ => return result

/-- Topologically sort metavariables so that each one's type only mentions
earlier ones; returns an empty array on a cyclic dependency, which well-typed
statements cannot produce. -/
private def sortMvars (mvars : Array MVarId) : MetaM (Array MVarId) := do
  let mut remaining : List MVarId := mvars.toList
  let mut sorted : Array MVarId := #[]
  let mut assigned : Array MVarId := #[]
  while !remaining.isEmpty do
    let mut progress := false
    let mut rest : List MVarId := []
    for mvarId in remaining do
      let type ← instantiateMVars (← mvarId.getType)
      let deps ← getMVars type
      if deps.all assigned.contains then
        sorted := sorted.push mvarId
        assigned := assigned.push mvarId
        progress := true
      else
        rest := mvarId :: rest
    unless progress do return #[]
    remaining := rest.reverse
  return sorted

/-- Assign every metavariable in `mvars` (in `sortMvars` order) a fresh local
and run `k` with all locals in scope; `k` receives them for final abstraction.
Retrieval terms hold metavariables at binder positions, and a metavariable can
only be assigned terms whose free variables are in its own local context, so
anything derived from the query must be created inside this scope. -/
private partial def withAnchorLocals (mvars : Array MVarId) (index : Nat)
    (locals : Array Expr) (k : Array Expr → MetaM α) : MetaM α := do
  if index == mvars.size then k locals
  else
    let mvarId := mvars[index]!
    let type ← instantiateMVars (← mvarId.getType)
    withLocalDeclD `vampireAnchor type fun anchorLocal => do
      mvarId.assign anchorLocal
      withAnchorLocals mvars (index + 1) (locals.push anchorLocal) k

/-- Bounded definitional variants of one query term:

* one-step unfoldings (`Meta.unfoldDefinition?`, `ignoreTransparency`) of
  constant-headed proper subterm arguments, so that sibling statements phrased
  over unfolded forms stay retrievable (e.g. `Finset.sup_mono` behind a
  `sup ∘ shatterer` bound); `ite`-headed arguments are skipped here, because
  their one-step delta is a `casesOn` term no entry is keyed on;
* one variant with every unfoldable argument unfolded at once;
* a definitional bridge for `ite`-headed arguments: `ite c t e` becomes
  `dite c (fun _ => t) (fun _ => e)`, the form the `Set.mem_dite_univ_left`
  family of statements is keyed on;
* pointwise instances of non-propositional function equalities: both sides are
  reduced to weak head normal form (a lambda for pointwise-lifted operations)
  and applied to a fresh metavariable, as the `_apply` family of statements is
  keyed on.

At most four subterm variants are added; the query term itself always comes
first. -/
private def anchorVariants (a : Expr) : MetaM (Array Expr) := do
  let mut out := #[a]
  match a.headBeta with
  | .app .. =>
    let e := a.headBeta
    let args := e.getAppArgs
    let mut anyUnfolded := false
    let mut deltaCount := 0
    for i in [0:args.size] do
      if deltaCount >= 4 then break
      let argument := args[i]!
      unless argument.isFVar || argument.isSort || argument.isMVar do
        if let .const head _ := argument.getAppFn then
          if head != ``ite && (← getEnv).contains head then
            if let some value ←
                try Meta.unfoldDefinition? argument (ignoreTransparency := true)
                catch _ => pure none
            then
              if value != argument then
                let rebuilt := mkAppN e.getAppFn (args.setIfInBounds i value)
                if rebuilt != a then
                  unless out.contains rebuilt do out := out.push rebuilt
                  deltaCount := deltaCount + 1
                anyUnfolded := true
    if anyUnfolded && args.size > 1 then
      let mut rebuiltArgs := args
      for i in [0:args.size] do
        let argument := args[i]!
        unless argument.isFVar || argument.isSort || argument.isMVar do
          if let .const head _ := argument.getAppFn then
            if head != ``ite && (← getEnv).contains head then
              if let some value ←
                  try Meta.unfoldDefinition? argument (ignoreTransparency := true)
                  catch _ => pure none
              then
                if value != argument then rebuiltArgs := rebuiltArgs.setIfInBounds i value
      let rebuilt := mkAppN e.getAppFn rebuiltArgs
      if rebuilt != a then unless out.contains rebuilt do out := out.push rebuilt
    for i in [0:args.size] do
      if deltaCount >= 4 then break
      let argument := args[i]!
      if argument.getAppNumArgs == 5 then
        if let .const ``ite levels := argument.getAppFn then
          let ty := argument.getAppArgs[0]!
          let c := argument.getAppArgs[1]!
          let inst := argument.getAppArgs[2]!
          let t := argument.getAppArgs[3]!
          let e' := argument.getAppArgs[4]!
          let thenLam := .lam Name.anonymous c t .default
          let elseLam := .lam Name.anonymous (mkApp (.const ``Not [.succ .zero]) c) e' .default
          let diteForm := mkAppN (.const ``dite levels) #[ty, c, inst, thenLam, elseLam]
          let rebuilt := mkAppN e.getAppFn (args.setIfInBounds i diteForm)
          if rebuilt != a then
            unless out.contains rebuilt do out := out.push rebuilt
            deltaCount := deltaCount + 1
  | _ => pure ()
  if let some (_, lhs, rhs) := a.eq? then
    unless ← isProp lhs do
      let lhsType ← instantiateMVars (← inferType lhs)
      if lhsType.isForall then
        try
          let domain := lhsType.bindingDomain!
          let argument ← mkFreshExprMVar domain
          let lhsD ← withTransparency .default <| whnf lhs
          let rhsD ← withTransparency .default <| whnf rhs
          let left :=
            if lhsD.isLambda then lhsD.bindingBody!.instantiate1 argument
            else (mkApp lhs argument).headBeta
          let right :=
            if rhsD.isLambda then rhsD.bindingBody!.instantiate1 argument
            else (mkApp rhs argument).headBeta
          let applied ← mkAppM ``Eq #[left, right]
          if applied != a then unless out.contains applied do out := out.push applied
          let appliedRaw ← mkAppM ``Eq #[(mkApp lhs argument).headBeta, (mkApp rhs argument).headBeta]
          if appliedRaw != a && appliedRaw != applied then
            unless out.contains appliedRaw do out := out.push appliedRaw
        catch _ => pure ()
  return out

/-- Instantiate one sibling candidate against a query term. The discrimination
tree only retrieves a superset; the pattern is the candidate's statement body,
or the corresponding side when the tree matched a biconditional subentry.

The query's metavariables are generalized to locals before acceptance: capture
commands elaborate against the fully quantified statement, so binder positions
enter as metavariables, and a fact that resolves them with the candidate's
parameters would keep them unresolved. The locals are abstracted in the final
fact, which re-quantifies them universally.

Statement sides are attempted cumulatively: an earlier side's unification
assignments may determine parameters that a later side closes. A failed
parameter closing only restores the state it saved — a failed closing assigns
parameters to locals that have left the scope, which would poison later
attempts — while the unification assignments are kept for the remaining
sides. -/
private def specialize (name : Name) (query : Expr)
    (mod : Lean.Meta.LibrarySearch.DeclMod) : MetaM (Option Auto.Lemma) := do
  let saved ← saveState
  try
    let anchorMvars ← sortMvars (← getMVars query)
    let result ← withAnchorLocals anchorMvars 0 #[] fun anchorLocals => do
      let proof ← mkConstWithFreshMVarLevels name
      let (parameters, _, body) ← forallMetaTelescope (← inferType proof)
      let proof := mkAppN proof parameters
      -- The tree keys the forward-direction subentry on the right-hand side of the
      -- statement and the backward one on the left-hand side (application arguments
      -- enter the key path outermost first), so try the indicated side first and
      -- keep the others as fallbacks: the tree only retrieves a superset.
      let patterns : Array Expr :=
        match body.iff? with
        | some (lhs, rhs) =>
          match mod with
          | .mp => #[rhs, lhs, body]
          | .mpr => #[lhs, rhs, body]
          | .none => #[body, rhs, lhs]
        | none => #[body]
      for pattern in patterns do
        unless ← AttributeLemmas.matchingHead pattern query do continue
        let defeqState ← saveState
        let reducible ←
          try withTransparency .reducible <| isDefEq pattern query
          catch _ => pure false
        unless reducible do
          -- Bounded fallback: definitional bridges (ite/dite, instance paths)
          -- only unify beyond reducible transparency. The failed reducible
          -- attempt may have left partial assignments behind.
          defeqState.restore
          let bridged ←
            try withTransparency .default <| isDefEq pattern query
            catch _ => pure false
          unless bridged do continue
        let preClose ← saveState
        let closed? ←
          try
            AttributeLemmas.closeParameters parameters 0 proof
          catch _ => pure none
        if let some proof := closed? then
          -- A fact whose top-level equality or biconditional sides coincide
          -- after specialization is trivial and adds nothing as a premise. The
          -- congruence schemata (`or_congr` and its family) accumulate the two
          -- statement sides, each determining only half the parameters, and
          -- would otherwise close with both sides instantiated identically.
          let instantiated ← instantiateMVars body
          let trivial :=
            match instantiated.iff?, instantiated.eq? with
            | some (l, r), _ => l == r
            | _, some (_, l, r) => l == r
            | _, _ => false
          unless trivial do
            let proof ← mkLambdaFVars anchorLocals proof
            let type ← inferType proof
            let lemma : Auto.Lemma := ⟨⟨proof, type, .leaf s!"{labelPrefix}{name}"⟩, #[]⟩
            let lemma ← Auto.unfoldConstAndPreprocessLemma #[] lemma
            let lemma ← SourceNormalization.normalizeLemma lemma
            return some lemma
        preClose.restore
      return none
    saved.restore
    return result
  catch _ =>
    saved.restore
    return none

/-- Whether any transitive constant dependency of the proof term mentions the
target theorem. This mirrors the audit rule that the theorem being reproved is
never a premise: an environment theorem proved from (or aliasing) the target
would let the prover restate the goal, and every proof using such a premise is
rejected. Types and proof values are both followed, exactly like the audit. -/
partial def dependsOnTarget (proof : Expr) (target : Name)
    (seen : IO.Ref (Std.HashSet Name)) : MetaM Bool := do
  let mut pending := proof.getUsedConstants
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if (← seen.get).contains name then continue
    seen.modify (·.insert name)
    if name == target then return true
    if let some info := (← getEnv).find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
  return false

/-- The body of `collect`: the bounded selection loop. -/
private def collectCore (lemmas : Array Auto.Lemma) (exclude? : Option Name)
    (limit : Nat) : MetaM (Array Auto.Lemma) := do
  let mut knownDomains : Std.HashSet Name := {}
  for lemma in lemmas do
    for name in (← AttributeLemmas.domainHeads lemma.type).toArray do
      knownDomains := knownDomains.insert name
  let mut result := #[]
  let mut attempted : Std.HashSet (Name × Expr) := {}
  let mut attempts := 0
  -- The memoized dependency walk is shared between candidates; it is discarded
  -- whenever the target is found, because that walk ends early and its set of
  -- fully explored constants is incomplete.
  let mut seen ← IO.mkRef ({} : Std.HashSet Name)
  for lemma in lemmas do
    if attempts >= 256 || result.size >= limit then break
    -- Heartbeat checks only fire inside operations, so a fresh attempt window
    -- would otherwise start after every burned one: checking here makes the
    -- enclosing collection window bind between attempts.
    checkSystem "sibling lemma collection"
    let sourceType ← instantiateMVars (← inferType lemma.proof)
    let first? ← attempt attemptBudget <| queries sourceType
    let second? ← attempt attemptBudget <| queries lemma.type (first?.getD #[])
    let terms := second?.getD (first?.getD #[])
    trace[vampire.premises] "sibling queries: {terms}"
    for anchor in terms do
      if attempts >= 256 || result.size >= limit then break
      checkSystem "sibling lemma collection"
      let variants? ← attempt attemptBudget <| anchorVariants anchor
      let variants := variants?.getD #[anchor]
      let mut anchorAttempts := 0
      for query in variants do
        if attempts >= 256 || result.size >= limit then break
        if anchorAttempts >= 32 then break
        checkSystem "sibling lemma collection"
        let saved ← saveState
        let candidates ←
          match ← attempt attemptBudget <| Lean.Meta.LibrarySearch.libSearchFindDecls query with
          | some candidates => pure candidates
          | none => do
            trace[vampire.premises] "sibling retrieval failed for {query}"
            saved.restore
            pure (#[] : Array (Name × LibrarySearch.DeclMod))
        trace[vampire.premises] "sibling query {query}: {candidates.size} candidates"
        for (name, mod) in candidates do
          if attempts >= 256 || result.size >= limit then break
          -- A single query can return a whole bucket of unrelated candidates;
          -- they must not consume the budget for the remaining anchors.
          if anchorAttempts >= 32 then break
          checkSystem "sibling lemma collection"
          if exclude? == some name then continue
          if attempted.contains (name, query) then continue
          attempted := attempted.insert (name, query)
          attempts := attempts + 1
          anchorAttempts := anchorAttempts + 1
          -- A storming specialization (a deep unification at default
          -- transparency) escapes its internal handlers — runtime exceptions are
          -- rethrown — so the attempt window plus the state restore here keep
          -- one bad candidate from poisoning the rest.
          let specSaved ← saveState
          let lemma?? ← attempt attemptBudget <| specialize name query mod
          let mut lemma? := lemma??.getD none
          if lemma?.isNone then specSaved.restore
          -- A variant may retrieve an entry whose statement matches the source
          -- proposition itself, so acceptance is attempted against the anchor
          -- as well; it is deduplicated like a direct attempt.
          if lemma?.isNone && query != anchor && !attempted.contains (name, anchor) then
            attempted := attempted.insert (name, anchor)
            let fallback? ← attempt attemptBudget <| specialize name anchor mod
            lemma? := fallback?.getD none
            if lemma?.isNone then specSaved.restore
          if let some lemma := lemma? then
            -- An environment theorem proved from the target, or an alias of it,
            -- would only restate the goal; every proof using it is rejected by
            -- the audit. Such candidates are refused before they enter the pool.
            if let some target := exclude? then
              if ← dependsOnTarget lemma.proof target seen then
                trace[vampire.premises] "Rejected sibling {name}: depends on {target}"
                seen ← IO.mkRef ({} : Std.HashSet Name)
                continue
            -- Do not introduce additional datatype theories incidentally.
            unless (← AttributeLemmas.domainHeads lemma.type).toArray.all knownDomains.contains do
              continue
            unless result.any (·.type == lemma.type) || lemmas.any (·.type == lemma.type) do
              trace[vampire.premises] "Selected sibling {name} for {query}"
              result := result.push lemma
  return result

/-- Discover unindexed sibling theorems for the propositions of the source
problem. Every accepted fact is a closed theorem reference instantiation; the
datatype-theory filter of the attribute collector is applied unchanged.

Sibling selection runs unattended inside the enclosing command's heartbeat
budget, where a deterministic timeout would abort the whole case: the command
dies, no result is recorded, and a proof the case could otherwise find is lost.
The collection therefore runs inside its own bounded window — and since the
core `MonadExcept` instance rethrows the deterministic timeout that a blown
window throws, every phase is contained with `tryCatchRuntimeEx`, so a blown
window only discards the sibling facts and restores the state, leaving the case
exactly as it behaves without them. When the enclosing command has little
headroom left, the collection is skipped up front: burning even the window
would leave the export, the search and the replay short of the budget they
need. -/
def collect (lemmas : Array Auto.Lemma) (exclude? : Option Name := none) :
    MetaM (Array Auto.Lemma) := do
  let options ← getOptions
  unless vampire.siblingLemmas.get options do return #[]
  let limit := vampire.siblingLemmaLimit.get options
  if limit == 0 then return #[]
  let coreCtx ← readThe Core.Context
  let entry ← IO.getNumHeartbeats
  let remaining := coreCtx.maxHeartbeats - (entry - coreCtx.initHeartbeats)
  if coreCtx.maxHeartbeats != 0 && remaining < headroomFloor then
    trace[vampire.premises] "sibling selection skipped: {remaining} of {coreCtx.maxHeartbeats} heartbeats left"
    return #[]
  -- The library-search import tree is built lazily by the first retrieval of
  -- the process, for far more heartbeats than one attempt window allows: a
  -- window that died mid-build would retry the whole build on every query. The
  -- index is therefore warmed once in its own window before the bounded loop;
  -- when the warmup fails, a later case of the same process retries it.
  unless (← attempt (min warmupBudget (remaining / 2)) <|
      Lean.Meta.LibrarySearch.libSearchFindDecls (mkConst ``True)).isSome do
    trace[vampire.premises] "sibling selection skipped: index warmup exceeded the window"
    return #[]
  let entry ← IO.getNumHeartbeats
  let remaining := coreCtx.maxHeartbeats - (entry - coreCtx.initHeartbeats)
  let budget :=
    if coreCtx.maxHeartbeats == 0 then siblingBudget
    else min siblingBudget (remaining / 4)
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      let result ← withHeartbeatBudget budget <| collectCore lemmas exclude? limit
      return result)
    (fun error => do
      saved.restore
      checkOptionalFailure error
      return #[])

end VampireHammer.SiblingLemmas

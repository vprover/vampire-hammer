import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-cache-search.py"
set_option vampire.directProof false
set_option vampire.decomposeGoals false
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option vampire.timeLimit 2
set_option trace.vampire.cache true
set_option linter.unusedVariables false

open Lean Meta Elab Tactic VampireHammer

universe u v

run_cmd do
  ProofCache.clear
  IO.FS.createDirAll "artifacts"
  for file in ["artifacts/session-cache.calls", "artifacts/session-cache.block"] do
    if ← System.FilePath.pathExists file then IO.FS.removeFile file

-- The first call really searches and replays a proof.
theorem cache_initial (α : Type u) (a : α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  vampire [h, hp]

run_cmd do
  let calls ← IO.FS.readFile "artifacts/session-cache.calls"
  unless calls.contains "search" do throwError "first call did not search"
  IO.FS.writeFile "artifacts/session-cache.before" calls
  IO.FS.writeFile "artifacts/session-cache.block" "block all subsequent external searches"

-- Fresh local IDs, renamed binders, and a different universe parameter name
-- must still reuse the complete proof. Every external search now fails.
theorem cache_renamed (β : Type v) (b : β) (R S : β → Prop)
    (rule : ∀ y, R y → S y) (positive : R b) : S b := by
  vampire [rule, positive]

example (β : Type v) (b : β) (R S : β → Prop)
    (rule : ∀ y, R y → S y) (positive : R b) : S b ∧ R b := by
  constructor
  · vampire [rule, positive]
  · exact positive

run_cmd do
  unless (← IO.FS.readFile "artifacts/session-cache.calls") ==
      (← IO.FS.readFile "artifacts/session-cache.before") do
    throwError "a cache hit launched Vampire"

-- Premise selection, the target, local hypothesis types, and proof-search
-- settings all participate in the key. Cache-disabled calls also search.
example (α : Type u) (a : α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  fail_if_success vampire []
  fail_if_success vampire (cache := false) [h, hp]
  fail_if_success vampire (disableAvatar := true) [h, hp]
  exact h a hp

example (α : Type u) (a : α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) : Q a ∧ Q a := by
  fail_if_success vampire [h, hp]
  exact ⟨h a hp, h a hp⟩

example (α : Type u) (a : α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hp : ∀ x, P x) : Q a := by
  fail_if_success vampire [h, hp]
  exact h a (hp a)

run_cmd ProofCache.clear

-- Clearing the cache forces the same call to search again.
example (α : Type u) (a : α) (P Q : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) : Q a := by
  fail_if_success vampire [h, hp]
  exact h a hp

-- Exercise closure over dependent locals and local lets without the prover.
-- The second action throws if called, so only a checked cache hit can solve it.
#eval show TermElabM Unit from do
  ProofCache.clear
  let run (mustHit : Bool) : TermElabM Unit := do
    withLocalDeclD `α (mkSort (.succ (.param `u))) fun α =>
      withLocalDeclD `a α fun a =>
        withLetDecl `b α a fun b => do
          let goal ← mkFreshExprMVar (← mkEq b a)
          discard <| Tactic.run goal.mvarId! do
            ProofCache.withCache (← `(Auto.hints|)) #[] do
              if mustHit then throwError "local-let proof was not cached"
              goal.mvarId!.assign (← mkEqRefl a)
          unless ← goal.mvarId!.isAssigned do throwError "cache left a goal"
  run false
  run true

-- Already-assigned metavariables in local declaration types are instantiated
-- before checking a hit; only genuinely unresolved ones should bypass caching.
#eval show TermElabM Unit from do
  ProofCache.clear
  let run (mustHit : Bool) : TermElabM Unit := do
    let type ← mkFreshExprMVar (mkSort (.succ .zero))
    type.mvarId!.assign (mkConst ``Nat)
    withLocalDeclD `n type fun n => do
      let goal ← mkFreshExprMVar (← mkEq n n)
      discard <| Tactic.run goal.mvarId! do
        ProofCache.withCache (← `(Auto.hints|)) #[] do
          if mustHit then throwError "assigned local type metavariable prevented reuse"
          goal.mvarId!.assign (← mkEqRefl n)
  run false
  run true

-- Auxiliary theorems made during reconstruction are inlined into the cached
-- proof, so they need not exist in the next elaboration's environment.
#eval show TermElabM Unit from do
  ProofCache.clear
  let original ← getEnv
  try
    let goal ← mkFreshExprMVar (mkConst ``True)
    discard <| Tactic.run goal.mvarId! do
      ProofCache.withCache (← `(Auto.hints|)) #[] do
        addDecl (.thmDecl {
          name := `cacheTransient
          levelParams := []
          type := mkConst ``True
          value := mkConst ``True.intro
        })
        goal.mvarId!.assign (mkConst `cacheTransient)
    setEnv original
    let goal ← mkFreshExprMVar (mkConst ``True)
    discard <| Tactic.run goal.mvarId! do
      ProofCache.withCache (← `(Auto.hints|)) #[] do
        throwError "proof cache retained a transient auxiliary theorem"
  finally
    setEnv original
    ProofCache.clear

-- Reusing a declaration name after an edit must invalidate the saved proof,
-- even when the declaration's type remains identical.
#eval show TermElabM Unit from do
  ProofCache.clear
  let original ← getEnv
  let attempts ← IO.mkRef 0
  try
    let run (value : Expr) : TermElabM Unit := do
      setEnv original
      addDecl (.thmDecl {
        name := `cacheDependency
        levelParams := []
        type := mkConst ``True
        value := value
      })
      let goal ← mkFreshExprMVar (mkConst ``True)
      discard <| Tactic.run goal.mvarId! do
        let identifier := mkIdent `cacheDependency
        ProofCache.withCache (← `(Auto.hints| [$identifier:ident])) #[] do
          attempts.modify (· + 1)
          goal.mvarId!.assign (mkConst `cacheDependency)
    run (mkConst ``True.intro)
    run (mkApp (mkLambda `x .default (mkConst ``True) (.bvar 0)) (mkConst ``True.intro))
    unless (← attempts.get) == 2 do throwError "changed declaration did not invalidate the cache"
  finally
    setEnv original
    ProofCache.clear

-- Changes behind an unchanged alias can escape the direct dependency check.
-- The kernel must still reject a saved term whose type no longer fits the goal.
#eval show TermElabM Unit from do
  ProofCache.clear
  let original ← getEnv
  let attempts ← IO.mkRef 0
  try
    let run (value : Nat) : TermElabM Unit := do
      setEnv original
      addDecl (.defnDecl {
        name := `cacheBase
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit value
        hints := .abbrev
        safety := .safe
      })
      addDecl (.defnDecl {
        name := `cacheAlias
        levelParams := []
        type := mkConst ``Nat
        value := mkConst `cacheBase
        hints := .abbrev
        safety := .safe
      })
      let goal ← mkFreshExprMVar (← mkEq (mkConst `cacheAlias) (mkNatLit 0))
      discard <| Tactic.run goal.mvarId! do
        ProofCache.withCache (← `(Auto.hints|)) #[] do
          attempts.modify (· + 1)
          if value == 0 then goal.mvarId!.assign (← mkEqRefl (mkNatLit 0))
    run 0
    run 1
    unless (← attempts.get) == 2 do throwError "cached proof was not checked against the new goal type"
  finally
    setEnv original
    ProofCache.clear

-- Unfold and defeq hints have distinct keys, while repeated identical hints hit.
#eval show TermElabM Unit from do
  ProofCache.clear
  let attempts ← IO.mkRef 0
  let run (uords : Array (TSyntax `Auto.uord)) (mustHit : Bool) : TermElabM Unit := do
    let goal ← mkFreshExprMVar (mkConst ``True)
    discard <| Tactic.run goal.mvarId! do
      ProofCache.withCache (← `(Auto.hints|)) uords do
        if mustHit then throwError "definition hints prevented reuse"
        attempts.modify (· + 1)
        goal.mvarId!.assign (mkConst ``True.intro)
  let unfolds ← `(Auto.uord| u[Nat.add])
  let defeqs ← `(Auto.uord| d[Nat.add])
  run #[unfolds] false
  run #[unfolds] true
  run #[defeqs] false
  run #[defeqs] true
  unless (← attempts.get) == 2 do throwError "unfold and defeq hints shared a key"
  ProofCache.clear

-- Complex hint terms bypass the cache, and incomplete actions never populate it.
#eval show TermElabM Unit from do
  ProofCache.clear
  let attempts ← IO.mkRef 0
  for _ in [:2] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    discard <| Tactic.run goal.mvarId! do
      ProofCache.withCache (← `(Auto.hints| [(by exact True.intro)])) #[] do
        attempts.modify (· + 1)
        goal.mvarId!.assign (mkConst ``True.intro)
  for _ in [:2] do
    let goal ← mkFreshExprMVar (mkConst ``True)
    discard <| Tactic.run goal.mvarId! do
      ProofCache.withCache (← `(Auto.hints|)) #[] do
        attempts.modify (· + 1)
    if ← goal.mvarId!.isAssigned then throwError "an incomplete proof was cached"
  unless (← attempts.get) == 4 do throwError "cache changed unsupported or incomplete actions"
  ProofCache.clear

#print axioms cache_initial
#print axioms cache_renamed

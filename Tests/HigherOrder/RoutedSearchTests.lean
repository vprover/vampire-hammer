import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false
set_option vampire.portfolioCores 1

set_option vampire.routedSlices false
run_cmd Lean.Elab.Command.modifyScope fun scope =>
  { scope with opts := scope.opts.set `vampire.internal.routedSearch true }
set_option vampire.directProof false
set_option vampire.decomposeGoals false
set_option vampire.timeLimit 10
set_option vampire.attributeLemmas false
set_option vampire.lawInstances false
set_option linter.unusedVariables false

open Lean Meta VampireHammer.Export.Internal

open Lean.Elab.Tactic
elab "with_internal_route " route:str " in " action:tacticSeq : tactic =>
  withOptions (·.set `vampire.internal.routeOverride route.getString) (evalTactic action)

/-! ### Structural features -/

private def routeOf (type : Expr) : MetaM (Routing.Route × Routing.Features × Bool) := do
  let proof ← mkFreshExprMVar type .syntheticOpaque
  Routing.choose #[{ proof, type, deriv := .leaf "test" }]

-- Function-typed constants and ordinary quantifiers alone stay first-order.
#eval show Elab.TermElabM Unit from do
  let type ← Elab.Term.elabType
    (← `(∀ (g : Nat → Nat) (x : Nat), g x = g x ∨ ∀ y : Nat, y = y))
  let (route, features, _) ← routeOf type
  unless features.boundFunctions == 1 && route == .firstOrder do
    throwError s!"bound function without further evidence routed {route.name}"

#eval show Elab.TermElabM Unit from do
  let type ← Elab.Term.elabType
    (← `(∀ (F : (Nat → Nat) → Nat) (f : Nat → Nat), F (fun x => f x) = F f))
  let (route, features, viable) ← routeOf type
  unless route == .higherOrder && viable && features.functionArguments ≥ 2 do
    throwError s!"expected native route, got {route.name}: {features.boundFunctions}/{features.functionArguments}"

-- Implications between propositions are not function types.
#eval show Elab.TermElabM Unit from do
  let type ← Elab.Term.elabType
    (← `(∀ (p q : Prop), (∀ n : Nat, n = n) → (p → q) → p → q))
  let (route, features, _) ← routeOf type
  unless features.boundFunctions == 0 && route == .firstOrder do
    throwError "proposition binder counted as a function"

-- An empty codomain without a cheap inhabitant prefers first-order.
#eval show Elab.TermElabM Unit from do
  let type ← Elab.Term.elabType
    (← `(∀ (F : (Nat → Empty) → Nat) (f : Nat → Empty), F (fun x => f x) = F f))
  let (route, _, viable) ← routeOf type
  unless route == .firstOrder && !viable do
    throwError "uninhabited function domain routed natively"

/-! ### Route switching -/

#eval show IO Unit from do
  IO.FS.createDirAll "artifacts"
  for mode in ["fallback", "fo-success"] do
    let result ← IO.Process.output { cmd := "ln", args := #["-sf",
      "../Tests/testdata/scripts/mock-staged-search.py", s!"artifacts/mock-routed-{mode}.py"] }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr

-- A first-order statement starts first-order; a timeout leaves the remainder to HO.
set_option vampire.executable "artifacts/mock-routed-fallback.py" in
set_option vampire.outputPath "artifacts/routed-fallback.p" in
theorem routed_fallback (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let fo ← IO.FS.readFile "artifacts/routed-fallback.p.fo-first.stderr"
  let ho ← IO.FS.readFile "artifacts/routed-fallback.p.stderr"
  unless fo.contains "stage: fo" do throw <| IO.userError "FO did not run first"
  let limit (text : String) := (text.splitOn "limit: ")[1]!.splitOn "d" |>.head! |>.toNat!
  unless fo.contains "limit: 100d" && ho.contains "stage: ho" && limit ho < 100 && limit ho > 90 do
    throw <| IO.userError "FO did not receive the whole budget or HO did not receive the remainder"

-- A successful first route never prepares or searches the other one.
set_option vampire.executable "artifacts/mock-routed-fo-success.py" in
set_option vampire.outputPath "artifacts/routed-fo-success.p" in
theorem routed_fo_success (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  if ← System.FilePath.pathExists "artifacts/routed-fo-success.p.fo-first.stdout" then
    throw <| IO.userError "route switched after a first-order success"
  let fo ← IO.FS.readFile "artifacts/routed-fo-success.p.stdout"
  unless fo.contains "SZS status Theorem" || fo.contains "SZS status Unsatisfiable" do
    throw <| IO.userError "FO proof missing"

-- The override starts native; a native success needs no first-order search.
set_option vampire.executable "artifacts/mock-routed-fallback.py" in
set_option vampire.outputPath "artifacts/routed-override.p" in
theorem routed_override (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  with_internal_route "ho" in vampire [h, hp]

#eval show IO Unit from do
  let text ← IO.FS.readFile "artifacts/routed-override.p"
  unless text.contains "thf(" do throw <| IO.userError "override did not start native"
  if ← System.FilePath.pathExists "artifacts/routed-override.p.ho-first.stdout" then
    throw <| IO.userError "native success switched route"

-- Neither route may turn a potentially empty domain into a contradiction.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh" in
example {α : Type} (P : α → Prop) (h : ∀ x, P x) (hn : ∀ x, ¬P x) : True := by
  fail_if_success have : False := by vampire [h, hn]
  trivial

/-! ### HO -> FO -> HO slices -/

#eval show IO Unit from do
  for mode in ["slices-fo", "slices-ho-retry", "slices-timeouts"] do
    let result ← IO.Process.output { cmd := "ln", args := #["-sf",
      "../Tests/testdata/scripts/mock-slice-search.py", s!"artifacts/mock-{mode}.py"] }
    unless result.exitCode == 0 do throw <| IO.userError result.stderr

-- HO times out in its 20% slice; FO proves in its 80% slice; HO is never retried.
set_option vampire.routedSlices true in
set_option vampire.executable "artifacts/mock-slices-fo.py" in
set_option vampire.outputPath "artifacts/slices-fo.p" in
theorem slices_fo (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let ho ← IO.FS.readFile "artifacts/slices-fo.p.ho-first.stderr"
  let fo ← IO.FS.readFile "artifacts/slices-fo.p.stderr"
  let limit (text : String) := (text.splitOn "limit: ")[1]!.splitOn "d" |>.head! |>.toNat!
  unless ho.contains "stage: ho" && ho.contains "limit: 20d" do
    throw <| IO.userError "first HO slice did not receive 20% of the budget"
  unless fo.contains "stage: fo" && limit fo > 70 do
    throw <| IO.userError "FO did not run after the HO slice"
  if ← System.FilePath.pathExists "artifacts/slices-fo.p.fo-second.stderr" then
    throw <| IO.userError "HO was retried after an FO success"

-- HO times out and FO ends early with a model: HO searches again with the alternate strategy.
set_option vampire.routedSlices true in
set_option vampire.executable "artifacts/mock-slices-ho-retry.py" in
set_option vampire.outputPath "artifacts/slices-ho-retry.p" in
theorem slices_ho_retry (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  vampire [h, hp]

#eval show IO Unit from do
  let fo ← IO.FS.readFile "artifacts/slices-ho-retry.p.fo-second.stderr"
  let ho ← IO.FS.readFile "artifacts/slices-ho-retry.p.stderr"
  unless fo.contains "stage: fo" && ho.contains "stage: ho" && ho.contains "--func_ext" do
    throw <| IO.userError "the final HO slice did not use the alternate strategy"

-- A timeout of FO is not an early failure: no third slice.
set_option vampire.routedSlices true in
set_option vampire.executable "artifacts/mock-slices-timeouts.py" in
set_option vampire.outputPath "artifacts/slices-timeouts.p" in
example (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (hp : P 0) : Q 0 := by
  fail_if_success vampire [h, hp]
  exact h 0 hp

#eval show IO Unit from do
  unless ← System.FilePath.pathExists "artifacts/slices-timeouts.p.ho-first.stderr" do
    throw <| IO.userError "first HO slice did not run"
  if ← System.FilePath.pathExists "artifacts/slices-timeouts.p.fo-second.stderr" then
    throw <| IO.userError "HO was retried after an FO timeout"

#print axioms routed_fallback
#print axioms routed_fo_success
#print axioms routed_override

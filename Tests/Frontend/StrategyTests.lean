import VampireHammer

-- Keep the route-specific protocol deterministic under the parallel default.
set_option vampire.parallel false

-- Exercise the single-route protocol independently of the default sliced search.
set_option vampire.routedSlices false

set_option vampire.executable "Tests/testdata/scripts/mock-strategy.sh"
set_option vampire.disableAvatar true
set_option vampire.timeLimit 7

private def assertArguments (path : String) (strategy : String) (portfolio : Bool := true)
    (proofExtra : String := "replay") (cores : Nat := 1) : IO Unit := do
  let output ← IO.FS.readFile (path ++ ".stdout")
  let actual := (output.splitOn "\n").filterMap fun line =>
    if line.startsWith "% Argument: " then some (line.drop 12 |>.toString) else none
  let decode := if strategy.isEmpty then [] else ["--decode", strategy]
  let mode := if strategy.isEmpty && portfolio then "portfolio" else "vampire"
  let expected := decode ++ ["--mode", mode, "--cores", toString cores, "--shuffle_input", "off",
    "--shuffle_on_schedule_repeats", "off", "--forced_options",
    "proof=tptp_ac:replay=on:skolemization=syntactic:shuffle_input=off:newcnf=off:avatar=off:proof_extra=" ++ proofExtra,
    "-p", "tptp_ac", "--replay", "on", "--skolemization", "syntactic",
    "--newcnf", "off",
    "--time_limit", "7",
    "--avatar", "off", "--proof_extra", proofExtra]
  unless actual == expected do
    throw <| IO.userError s!"Unexpected Vampire arguments: {actual}; expected {expected}"

-- Replay settings, including syntactic Skolemization, are passed without a strategy too.
set_option vampire.outputPath "artifacts/strategy-default.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire [parent, notP]

#eval assertArguments "artifacts/strategy-default.p" ""

-- Vampire worker counts are independent of tactic-level parallel execution.
set_option vampire.outputPath "artifacts/strategy-workers.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (portfolioCores := 3) [parent, notP]

#eval assertArguments "artifacts/strategy-workers.p" "" (cores := 3)

-- Zero is forwarded to Vampire's automatic worker selection (the mock does
-- not actually start workers).
set_option vampire.outputPath "artifacts/strategy-auto-workers.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (portfolioCores := 0) [parent, notP]

#eval assertArguments "artifacts/strategy-auto-workers.p" "" (cores := 0)

set_option vampire.strategy "lrs+10_1_100"

-- Forward the complete inline strategy as one argument, overriding the option.
set_option vampire.outputPath "artifacts/strategy-inline.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "lrs-1002_1_to=kbo:sil=2000:wl=60:uwa=off:updr=off:random_seed=216370:i=641:sd=20:hb=500:qa=off:ss=axioms:sgt=8_4") [parent, notP]

#eval assertArguments "artifacts/strategy-inline.p"
  "lrs-1002_1_to=kbo:sil=2000:wl=60:uwa=off:updr=off:random_seed=216370:i=641:sd=20:hb=500:qa=off:ss=axioms:sgt=8_4"

-- An empty inline strategy explicitly disables the configured strategy.
set_option vampire.outputPath "artifacts/strategy-empty.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "") [parent, notP]

#eval assertArguments "artifacts/strategy-empty.p" ""

-- Inline overrides do not leak into subsequent calls.
set_option vampire.outputPath "artifacts/strategy-option.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire [parent, notP]

#eval assertArguments "artifacts/strategy-option.p" "lrs+10_1_100"

-- Explicit opt-out retains ordinary Vampire mode without an encoded strategy.
set_option vampire.use_portfolio false in
set_option vampire.outputPath "artifacts/strategy-single.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "") [parent, notP]

#eval assertArguments "artifacts/strategy-single.p" "" false

-- The public option explicitly re-enables the one-worker portfolio.
set_option vampire.use_portfolio true in
set_option vampire.outputPath "artifacts/strategy-portfolio.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "") [parent, notP]

#eval assertArguments "artifacts/strategy-portfolio.p" "" true

-- Encoded integrated-CNF settings cannot remove required Skolem certificates.
set_option vampire.outputPath "artifacts/strategy-newcnf.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "lrs+10_1_newcnf=on") [parent, notP]

#eval assertArguments "artifacts/strategy-newcnf.p" "lrs+10_1_newcnf=on"

-- Older custom builds can retain their certificate-detail spelling.
set_option vampire.proofExtra "avatar_split" in
set_option vampire.outputPath "artifacts/strategy-legacy-certificates.p" in
example {α : Type} (a : α) (P : α → Prop)
    (parent : ∀ x, x ≠ a ∨ P x) (notP : ¬ P a) : False := by
  vampire (strategy := "") [parent, notP]

#eval assertArguments "artifacts/strategy-legacy-certificates.p" "" true "avatar_split"

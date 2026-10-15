# VampireHammer options and defaults

This reference covers every core `vampire.*` option registered by this repository,
plus tactic settings, trace switches, internal search keys, and Lake build
settings. Defaults below are declaration defaults; individual search routes
may override them as described below. Dependency options belonging to Lean,
lean-auto, or Vampire itself, and optional benchmark-only settings, are outside
this reference.

## Setting options

Import `VampireHammer` before using the tactic and its options. Set a default
for subsequent declarations with `set_option`, or scope it to one declaration
with `in`:

```lean
import VampireHammer

set_option vampire.timeLimit 20
set_option vampire.quiet true in
example (P : Prop) (h : P) : P := by
  vampire [h]
```

For one tactic call, omit the `vampire.` prefix and put settings before or
after the premise list. Inline values must be literals: `true`/`false`,
natural numbers, or quoted strings, according to the option's type.
Later settings of the same option override earlier settings in that call.

```lean
example (P : Prop) (h : P) : P := by
  vampire (timeout := 20) [h] (quiet := true)
```

The same inline syntax is available to `vampire_export`, which exports the
problem through `vampire.mockScript` and leaves the goal unchanged.
`vampire_capture` is a deprecated spelling of `vampire`.

| Tactic setting | Default | Meaning |
| --- | --- | --- |
| `timeout := n` | `10` | Alias for `timeLimit := n`, in seconds. |
| `unfold := [c, ...]` | No explicit unfold hints | Unfold the named definitions before translation. |
| `defeq := [c, ...]` | No explicit equation hints | Add definitional equations for the named constants. |
| `key := value` | The current `vampire.key` value | Override any registered option available in the imported environment, for example `(disableAvatar := true)`. |

Facts such as `[h₁, h₂, Nat.add_comm]` select premises; `[*]` selects all
local hypotheses. They are separate from settings.

## Parallel search

```lean
vampire [h₁, h₂]                       -- parallel, one worker per portfolio
vampire (portfolioCores := 2) [h₁, h₂] -- parallel, two workers per portfolio
```

`parallel` is enabled by default and overrides the sliced schedule. The original goal shares one
monomorphization between native HO and checked FO; each route independently
exports, searches and replays. If `decomposeGoals` is enabled and the goal
can split, a concurrent attempt prepares the split goals, with a separate
monomorphization for each leaf. Leaves are solved in sequence, each racing
FO and HO with the split attempt's remaining budget.

The first successful replay commits its Lean state and cancels and joins the
other attempts. A failed export, search or replay does not prevent another
route from winning. Each attempt receives the full search allowance rather
than a percentage slice; split leaves share their attempt's allowance.
`timeout := 0` permits unlimited parallel search. Lean heartbeat limits still
apply to preparation and replay. Slice percentages, decomposition reserves,
plain/library-suggestion slices and `monoHeartbeats` are unused in this mode.

`portfolioCores` controls Vampire's `--cores` in FO portfolio mode: `1` keeps
one worker, a larger number enables concurrent workers, and `0` uses all
available cores. It applies with or without `parallel`. Native HO uses a
single search process. In single-route mode, an explicit encoded strategy
also uses one process. In parallel mode, an encoded strategy applies to HO;
FO uses its default search configuration, as in routed search.
With parallel goal decomposition, both the original goal and the current
split leaf can each run a portfolio and an HO process concurrently.

When `outputPath` is set, parallel routes use `.fo.p` and `.ho.p` suffixes.
The decomposition attempt adds `.split.branch-N.p` before the route suffix,
so concurrent attempts retain separate inputs, outputs and event logs.

## Session proof cache

`cache` defaults to `true`. Each Lean process keeps up to 128 completed Lean
proof terms in memory. A matching call instantiates the saved proof in the
current local context and checks the entire term with Lean's kernel before
using it. A hit skips fact collection, monomorphization, Vampire and replay.
No prover output or cache files are written to disk.

The key includes the goal, local context (including local let values), resolved
identifier premises, unfold/defeq settings and Vampire/lean-auto options. Fresh local IDs,
binder names and universe-parameter names do not prevent reuse. Referenced
declarations are checked against the current environment; invalid entries fall
back to ordinary proof search. Temporary helper theorems created during replay
are inlined into the cached term.

Calls with complex premise expressions (such as `[h a]` or `[by ...]`), premise
databases, or unresolved metavariables bypass the cache. This avoids elaborating
user-provided terms twice. Failed, incomplete and `sorry` proofs are not stored.
The cache disappears when the Lean worker restarts and is not shared between
separate Lean processes.

```lean
set_option trace.vampire.cache true -- report hits, misses and bypasses
-- Force search even if the proof is cached:
example (p : Prop) (h : p) : p := by vampire (cache := false) [h]
-- Clear every entry in this Lean process:
run_cmd VampireHammer.ProofCache.clear
```

Disable caching when benchmarking or collecting fresh prover artifacts and
timings. Cache hits do not launch Vampire or rewrite its output artifacts.

## Units and constraints

- `timeLimit` is an external proof-search allowance in **seconds**, per attempt
  in parallel mode and shared in sequential mode. It is not a wall-clock limit
  for the whole tactic. Translation and proof reconstruction also consume
  Lean's heartbeat budget.
- `satPrecheck` is in **deciseconds**: `10` requests one second.
- Heartbeat options use Lean's user-facing units, each representing **1,000
  internal heartbeats**. These measure computation, not elapsed seconds.
  Optional direct-proof, data-witness, and domain-witness searches also cap
  each allowance at half the caller's remaining heartbeats.
- `plainSliceShare`, `higherOrderSliceShare`, `sliceHoFirst`, `sliceFo`,
  `sliceFoBeforeRecovery`, and `decompositionReserve` must be between `0`
  and `100`. Additionally, `sliceHoFirst + sliceFo` must be at most `100`.
- `timeLimit := 0` permits unlimited parallel search. In sequential mode,
  unlimited search requires `routedSlices := false`. Other zero values have
  option-specific meanings listed below.

## Search and scheduling

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.timeLimit` | `Nat` | `10` | External proof-search allowance in seconds, per attempt in parallel mode and shared in sequential mode (0 means unlimited; sequential routedSlices requires a positive budget) |
| `vampire.parallel` | `Bool` | `true` | Race native HO and checked FO search after shared monomorphization, and concurrently try goal decomposition when enabled; overrides routedSlices |
| `vampire.routedSlices` | `Bool` | `true` | Time-sliced HO -> FO -> HO schedule over one shared monomorphization: native HO searches its share first, FO then searches its share plus any time HO left unspent, and HO searches again with the alternate strategy only if FO ended early (finite model, GaveUp or another failure, not a timeout) and HO had been prepared (requires a finite timeLimit; ignores monoHeartbeats) |
| `vampire.sliceHoFirst` | `Nat` | `20` | Percentage of the search budget for the first native HO slice of routedSlices |
| `vampire.sliceFo` | `Nat` | `80` | Percentage of the search budget for the FO slice of routedSlices (plus unspent time of the first HO slice) |
| `vampire.sliceFoBeforeRecovery` | `Nat` | `10` | Percentage of the search budget for the first-order slice when the native slice failed on a missing domain; the tactic's inhabitant recovery then retries with the remaining time |
| `vampire.decompositionReserve` | `Nat` | `30` | With routedSlices, percentage of the search budget held back from the main attempt for goal decomposition when the goal is one it can split; unspent main time is returned to it |
| `vampire.higherOrder` | `Bool` | `false` | When parallel and routedSlices are disabled, select native higher-order THF (true) or first-order TFF (false); also controls export-only calls |
| `vampire.higherOrderFallback` | `Bool` | `false` | Retry failed native higher-order problems with the checked first-order encoding |
| `vampire.higherOrderSliceShare` | `Nat` | `75` | Percentage of the remaining search budget for native higher-order search before a first-order retry |
| `vampire.higherOrderSearchRetry` | `Bool` | `true` | Retry a fast native HO GaveUp with extensionality and heuristic instantiation, using only unspent search time |
| `vampire.strategy` | `String` | `""` | Encoded strategy passed to Vampire with `--decode` |
| `vampire.use_portfolio` | `Bool` | `true` | Use Vampire portfolio mode when vampire.strategy is empty |
| `vampire.portfolioCores` | `Nat` | `1` | Number of Vampire portfolio workers (0 uses all available cores); applies when use_portfolio is true and strategy is empty |
| `vampire.satPrecheck` | `Nat` | `0` | Finite model building run before proof search, in deciseconds (0 disables) |
| `vampire.plainSliceShare` | `Nat` | `50` | Percentage of the search budget for the attempt without library suggestions |

With `parallel := false`, routed search prepares first-order (FO) and native higher-order
(HO) representations together, tries HO with 20% of the available search
budget, then FO with 80% plus unspent HO time. A final alternate HO attempt
uses remaining time only if FO finishes early and HO preparation succeeded.
For a splittable goal, `decompositionReserve` holds back 30% before this
main attempt; decomposition can also use time the main attempt leaves over.

With parallel search disabled and `routedSlices := true`, the schedule chooses its own representations,
so `higherOrder` does not force it to stay on HO or FO, and `monoHeartbeats`
is ignored. To select a single route, set `parallel := false` and
`routedSlices := false`, then choose
`higherOrder`. Export-only calls also use `higherOrder` to choose THF or TFF.
`higherOrderFallback` and `higherOrderSliceShare` configure the HO-to-FO retry
outside parallel and routed search. `higherOrderSearchRetry` permits a fast
HO `GaveUp` to retry with extensionality and heuristic instantiation.

A nonempty `strategy` is passed with `--decode`. `use_portfolio` applies to
FO search when no encoded strategy is supplied; native HO uses its own search
configuration. In sequential mode, `plainSliceShare` matters when
`suggestedLemmas > 0`: first
try without library suggestions, then retry with suggestions and the unspent
budget. Set `plainSliceShare := 0` to skip that initial plain attempt.

## Premise selection and direct proofs

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.attributeLemmas` | `Bool` | `true` | Select relevant simp and grind theorem instances for the TF0 problem |
| `vampire.attributeLemmaLimit` | `Nat` | `16` | Maximum automatically selected simp/grind theorem instances |
| `vampire.attributeLemmaRounds` | `Nat` | `1` | Bounded rounds of premise discovery at newly exposed terms (at most four) |
| `vampire.definitionLemmas` | `Bool` | `false` | Include compiler-generated defining equations in bounded premise discovery |
| `vampire.siblingLemmas` | `Bool` | `false` | Select plain environment theorems whose statements mention propositions of the source problem |
| `vampire.siblingLemmaLimit` | `Nat` | `16` | Maximum automatically selected sibling theorem instances |
| `vampire.suggestedLemmas` | `Nat` | `0` | Maximum theorems taken from Lean's library-suggestion engine (0 disables) |
| `vampire.lawInstances` | `Bool` | `true` | Discover Std law instances for source operations and add their laws as facts |
| `vampire.objectLaws` | `Bool` | `false` | Instantiate object-quantified local laws at the problem's objects (experimental) |
| `vampire.dataWitnesses` | `Bool` | `true` | Instantiate data arguments of explicit premises with non-proposition hints and local data |
| `vampire.dataWitnessHeartbeats` | `Nat` | `4000` | Shared heartbeat allowance for optional data-witness instantiation (0 disables it) |
| `vampire.directProof` | `Bool` | `true` | Try to close the goal from the selected facts without translation before calling Vampire |
| `vampire.directProofHeartbeats` | `Nat` | `2000` | Shared heartbeat allowance for optional direct proof attempts (0 disables them) |

`attributeLemmaRounds` is clamped to the range 1–4; `0` still means one
round. Use `attributeLemmas := false` to disable that discovery.
`definitionLemmas` extends that discovery with compiler-generated equations.
Library suggestions and sibling theorem selection are disabled by default.

`dataWitnessHeartbeats := 0` and `directProofHeartbeats := 0` disable their
respective optional searches. Direct proofs may solve a goal before any
external prover is started.

## Goal preparation and translation

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.exposeGoalBinders` | `Bool` | `true` | Expose definitionally hidden universal binders before negating the goal |
| `vampire.decomposeGoals` | `Bool` | `true` | Try bounded constructor and extensionality decomposition after the original export attempt |
| `vampire.decompositionGoalLimit` | `Nat` | `8` | Maximum generated subgoals in structural goal preparation |
| `vampire.monoDecomposition` | `Bool` | `true` | Try bounded constructor decomposition before the HO retry when the default/sliced FO monomorphization window expires |
| `vampire.monoHeartbeats` | `Nat` | `0` | Heartbeat window for first-order monomorphization; on exhaustion the attempt is retried natively higher-order without constant-specialization saturation (0 disables both) |
| `vampire.autoUnfold` | `Bool` | `true` | Unfold definitions whose applications require higher-order TF0 arguments |
| `vampire.autoUnfoldLimit` | `Nat` | `32` | Maximum automatic definition expansions per source fact |
| `vampire.unfoldingPlan` | `Bool` | `true` | Decide once per problem which definitions to unfold and unfold them in every fact (see `VampireHammer.UnfoldingPlan`), instead of within each fact separately |
| `vampire.normalizeProofArguments` | `Bool` | `true` | Reduce definitionally redundant proof arguments and reflexive equality transports |
| `vampire.alignNestedDefinitions` | `Bool` | `true` | Align logical definitions nested in the goal with the same definitions in selected facts |
| `vampire.alignInstantiatedDefinitions` | `Bool` | `true` | After monomorphization, expand definitions that were unfolded in the goal or occur on only one side of the problem in every instantiated fact, and add their instantiated defining equations |
| `vampire.definitionalInverses` | `Bool` | `true` | Add `∀ x, g (f x) = x` for unary functions of the instantiated problem that are inverse by definitional unfolding |
| `vampire.relativizeSubtypes` | `Bool` | `true` | Relativize quantifiers over subtypes to their base type |
| `vampire.higherOrderEncoding` | `Bool` | `true` | Use checked object encoding for function/proposition values, conditionals and quantifiers without known domain witnesses when ordinary TF0 translation rejects them |
| `vampire.deferInhabitants` | `Bool` | `true` | Assume `Nonempty α` for a type variable without inhabitant and discharge the assumption only if the proof uses it |
| `vampire.domainWitnessHeartbeats` | `Nat` | `4000` | Shared heartbeat allowance for optional local domain witness recovery per problem |
| `vampire.omitUnsupportedLocalHypotheses` | `Bool` | `true` | After a monomorphization failure, retry while omitting unrepresentable local hypothesis instances |
| `vampire.normalizeCoercions` | `Bool` | `true` | Add copies of instantiated facts whose coercions are in simp normal form |
| `vampire.coercionLaws` | `Bool` | `true` | Add extensionality and coercion injectivity for each bundled coercion of the problem |
| `vampire.coercionBridges` | `Bool` | `true` | Relate coerced bundled maps to the plain functions of the problem (from bundled-map hints and `@[simp]` coercion lemmas) |
| `vampire.projectionDefinitions` | `Bool` | `true` | Add the defining equations of structure projections applied to definitions whose body is a structure literal |
| `vampire.instanceDefinitions` | `Bool` | `true` | Add the defining equivalence of proposition-valued class operations whose instance is declared in the current module and reduces to a logical formula |

`monoHeartbeats := 0` disables the local monomorphization window and its
associated retry. With a positive window on the applicable FO route,
exhaustion can trigger bounded constructor decomposition followed by a
native HO retry without constant-specialization saturation. This retry may
lose useful dependent or polymorphic instances. `monoDecomposition` requires
`decomposeGoals` and is inactive under parallel or routed search.

`decompositionGoalLimit := 0` disables goal decomposition.
`domainWitnessHeartbeats := 0` disables optional local domain-witness recovery.
`deferInhabitants` only defers an inhabitance assumption: a proof that uses
it must still discharge it. Omitting unsupported hypotheses weakens the
problem; retained premises still carry checked Lean proofs.

## Proof certificates and replay

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.disableAvatar` | `Bool` | `false` | Pass `--avatar off` to request a non-AVATAR Vampire proof |
| `vampire.avatarSplitCertificate` | `Bool` | `true` | Request replay certificates through `--proof_extra` |
| `vampire.proofExtra` | `String` | `"replay"` | Vampire proof_extra value when replay certificates are enabled |
| `vampire.structural` | `Bool` | `true` | reconstruct preprocessing steps and AVATAR splits structurally before falling back to the simp-based tactics |
| `vampire.satReplayLimit` | `Nat` | `96` | SAT replay node budget before falling back to bv_decide (0 disables replay) |
| `vampire.satLratReplayLimit` | `Nat` | `4096` | SAT trail node budget for checked LRAT reflection (0 disables it) |
| `vampire.grindMaxHeartbeats` | `Nat` | `100000` | Heartbeat limit (in thousands) for each `grind` fallback step; 0 uses only the enclosing limit |

Native HO search turns AVATAR off regardless of `disableAvatar`.
`proofExtra` is used only when `avatarSplitCertificate` is enabled; `replay`
is the current default, while older custom prover builds may need
`"avatar_split"`.

Small supplied SAT trails can use proof-producing replay; larger RUP trails
can use checked LRAT reflection. If these methods decline, the checked
boundary clauses can fall back to `bv_decide`. Setting either SAT limit to
`0` disables that method, rather than disabling SAT closure altogether.
`grindMaxHeartbeats := 0` removes the extra per-step limit but retains any
enclosing Lean limit.

## Output, executables, and export

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.quiet` | `Bool` | `true` | Suppress the success message after vampire closes the goal (errors are still reported) |
| `vampire.cache` | `Bool` | `true` | Reuse completed kernel-checked Lean proofs from a bounded in-memory cache in this Lean process |
| `vampire.executable` | `String` | `""` | Path to the Vampire executable (empty: the package-built Vampire, else `vampire` on PATH) |
| `vampire.outputPath` | `String` | `""` | If set, save the TPTP input here and raw Vampire output beside it |
| `vampire.mockScript` | `String` | `"Tests/testdata/scripts/mock-vampire.sh"` | Shell script that captures the TPTP problem on stdin |
| `vampire.tptpParserDynlib` | `String` | `""` | Shared library implementing the TPTP parser (empty: the one built with this package) |
| `vampire.diagnosticCase` | `String` | `""` | Case identity attached to durable diagnostic events in batched benchmarks |

With `outputPath := ""`, ordinary proof calls write no diagnostic files.
A nonempty base path saves input and raw `.stdout`/`.stderr` output, plus
`.events.jsonl` diagnostic events. Retries and decomposed branches can add
suffixes to that path. `diagnosticCase` labels events; a nonempty case also
prints diagnostic event lines to stderr when output is enabled.

`vampire_export` invokes `/bin/sh` with `mockScript` and the destination path
as its first argument, sending the generated TPTP problem on stdin. Its
fallback destination is `artifacts/example.p`. The default capture script
must exist; selecting `outputPath` alone does not provide that script.
`quiet` suppresses the success message for proof calls; errors remain visible.


## Internal registered options

The tactic fills these strings while preparing a query. They are listed
for completeness; normally leave them at their defaults. Names are stored
as space-separated strings.

| Option | Type | Default | Effect |
| --- | --- | --- | --- |
| `vampire.goalDefinitions` | `String` | `""` | Internal: definitions unfolded while introducing the current goal |
| `vampire.foldedDefinitions` | `String` | `""` | Internal: definitions concluded by the explicit premises of the current query |

## Trace switches

All registered trace switches default to `false`. Enable them with
`set_option trace.vampire.replay true`, for example. These use Lean's trace
system and are not inline `vampire` settings.

| Switch | What it shows |
| --- | --- |
| `trace.vampire` | General translation, search, process, and retry diagnostics. |
| `trace.vampire.unfold` | Definition unfolding and source normalization. |
| `trace.vampire.premises` | Automatic premise selection. |
| `trace.vampire.replay` | Proof decoding and reconstruction diagnostics. |
| `trace.vampire.cache` | Session proof-cache hits, misses, and bypasses. |
| `trace.vampire.bridge` | Diagnostics for the `vampire_bridge` interface. |

## Internal search keys

The following implementation-test keys are deliberately **unregistered**.
They cannot be configured with `set_option` or inline tactic settings;
implementation tests set them programmatically in `Lean.Options`.

| Key | Type | Default | Purpose |
| --- | --- | --- | --- |
| `vampire.internal.stagedSearch` | `Bool` | `false` | Select the experimental staged search schedule. |
| `vampire.internal.routedSearch` | `Bool` | `false` | Select the experimental routed search schedule. |
| `vampire.internal.routeOverride` | `String` | `""` | Override experimental route selection in implementation tests. |
| `vampire.internal.prepareHigherOrderAsync` | `Bool` | `true` | Prepare the experimental higher-order representation asynchronously. |

## Lake build settings

These settings come from the root [lakefile.lean](../lakefile.lean). They
configure the bundled prover build, independently of Lean tactic options.
For a checkout of this package, pass them with `-K` and reload configuration
with `-R`:

```sh
lake -R -KbuildVampire=false build
lake -R -KvampireJobs=4 build vampire
```

| Setting | Default | Effect |
| --- | --- | --- |
| `buildVampire` | `true` | Build the bundled prover. Only the string `false` disables the target's clone/build work. |
| `mathlib` | `false` | The string `true` includes mathlib at `v4.34.1` and enables the Mathlib benchmark library. The test runner sets this for Mathlib tests. |
| `vampireRepository` | `"https://github.com/vprover/vampire"` | Repository from which the pinned Vampire commit is fetched. |
| `vampireStatic` | `false` | The string `true` selects static linking (`BUILD_SHARED_LIBS=OFF`); other values select dynamic linking. |
| `vampireJobs` | Automatic | Maximum parallel build jobs. A parsed natural number is clamped to at least 1; missing or invalid values use the automatic calculation. |

Automatic jobs are the available core count capped at one job per 2 GiB of
available memory, with at least one job. On macOS the memory estimate uses
half the total memory. If memory cannot be determined, the core count is
used. The core-count fallback is 1.

Vampire is pinned to commit `6ee1f120df1b6c38705066dcbe7c858c09b12ded`
from the `tptp-replay-annotations` branch. The `vampireRevision` constant in
`lakefile.lean` records the pin; it is not a `-K` setting. Fresh builds fetch
that commit directly, and existing checkouts at another commit are switched
to the pin without forcing local changes. Deleting `.lake/vampire` rebuilds
the same pinned version.

Before configuring CMake, the build initializes `cadical` and `viras` and
recovers submodule clones interrupted before their initial checkout.

## Sources

Defaults and descriptions are defined in [Options.lean](../VampireHammer/Options.lean)
and the `register_option` declarations throughout `VampireHammer/`.
Inline syntax and validation are defined in [Tactic.lean](../VampireHammer/Tactic.lean).
Search scheduling is implemented in [Export/Pipeline.lean](../VampireHammer/Export/Pipeline.lean),
and heartbeat units and optional allowances in
[Export/SearchBudget.lean](../VampireHammer/Export/SearchBudget.lean).

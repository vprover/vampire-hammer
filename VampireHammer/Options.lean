import Lean

/-!
Options shared by the export and capture tactics. Registration names and defaults are the public
configuration interface.
-/

open Lean

register_option vampire.onlyFacts : Bool := {
  defValue := false
  descr := "Internal: restrict vampire only to selected source facts"
}

register_option vampire.quiet : Bool := {
  defValue := true
  descr := "Suppress the success message after vampire closes the goal (errors are still reported)"
}

register_option vampire.reportFacts : Bool := {
  defValue := true
  descr := "Report automatically added premises used by the completed proof"
}

register_option vampire.cache : Bool := {
  defValue := true
  descr := "Reuse completed kernel-checked Lean proofs from a bounded in-memory cache in this Lean process"
}

/-- Script used only by `vampire_export`. It receives the generated TPTP text
on stdin and the configured output path as its first argument. -/
register_option vampire.mockScript : String := {
  defValue := "Tests/testdata/scripts/mock-vampire.sh"
  descr := "Shell script that captures the TPTP problem on stdin"
}

/-- Base path for the generated TF0 input and raw process artifacts. Vampire
always communicates through stdin/stdout; these files are only diagnostics.
Empty (the default) writes nothing, except that `vampire_export` falls back to
`artifacts/example.p`. -/
register_option vampire.outputPath : String := {
  defValue := ""
  descr := "If set, save the TPTP input here and raw Vampire output beside it"
}

/-- Program invoked by `vampire`; normally the Vampire binary. Empty
selects the binary built by this package (`lake build vampire`), falling back
to `vampire` on `PATH`. -/
register_option vampire.executable : String := {
  defValue := ""
  descr := "Path to the Vampire executable (empty: the package-built Vampire, else `vampire` on PATH)"
}

/-- Encoded Vampire strategy; an empty string uses the configured search mode. -/
register_option vampire.strategy : String := {
  defValue := ""
  descr := "Encoded strategy passed to Vampire with `--decode`"
}

/-- Use a portfolio when no encoded strategy is supplied. -/
register_option vampire.use_portfolio : Bool := {
  defValue := true
  descr := "Use Vampire portfolio mode when vampire.strategy is empty"
}

register_option vampire.portfolioCores : Nat := {
  defValue := 0
  descr := "Maximum workers per FO portfolio (0 fills its processor allocation); parallel search reserves one processor for HO and divides processors between direct and split searches"
}

register_option vampire.parallel : Bool := {
  defValue := true
  descr := "Race native HO and checked FO search after shared monomorphization, and concurrently try goal decomposition when enabled; overrides routedSlices"
}

/-- Collect algebraic laws from `Std` law instances for the binary operations
occurring in the requested source facts. -/
register_option vampire.lawInstances : Bool := {
  defValue := true
  descr := "Discover Std law instances for source operations and add their laws as facts"
}

/-- Maximum number of seconds Vampire may spend searching for a proof. -/
register_option vampire.timeLimit : Nat := {
  defValue := 10
  descr := "External proof-search allowance in seconds, per attempt in parallel mode and shared in sequential mode (0 means unlimited; sequential routedSlices requires a positive budget)"
}

/-- Most failed hammer problems are satisfiable abstractions on which saturation
never terminates. A short finite-model-building run recognizes many of them,
leaving the search budget to later attempts. -/
register_option vampire.satPrecheck : Nat := {
  defValue := 0
  descr := "Finite model building run before proof search, in deciseconds (0 disables)"
}

/-- AVATAR introduces fresh split predicates and ends the proof with a SAT
refutation. Replay treats its definitions as proof-local propositions and
rederives the propositional contradiction with `bv_decide`. This option still
allows examples focused on first-order rules to request a proof without AVATAR. -/
register_option vampire.disableAvatar : Bool := {
  defValue := false
  descr := "Pass `--avatar off` to request a non-AVATAR Vampire proof"
}

/-- Ask Vampire to annotate `avatar_split_clause` nodes with the definition
binders used after expansion. This turns otherwise implicit universal-variable
permutations into a replayable certificate. -/
register_option vampire.avatarSplitCertificate : Bool := {
  defValue := true
  descr := "Request replay certificates through `--proof_extra`"
}

/-- Certificate detail level used by current Vampire builds. Older custom
builds used `avatar_split`; callers can select that spelling explicitly. -/
register_option vampire.proofExtra : String := {
  defValue := "replay"
  descr := "Vampire proof_extra value when replay certificates are enabled"
}

register_option vampire.higherOrderEncoding : Bool := {
  defValue := true
  descr := "Use checked object encoding for function/proposition values, conditionals and quantifiers without known domain witnesses when ordinary TF0 translation rejects them"
}

register_option vampire.deferInhabitants : Bool := {
  defValue := true
  descr := "Assume `Nonempty α` for a type variable without inhabitant and discharge the assumption only if the proof uses it"
}

/-- Representation of the single-route search and export-only tactic.
Parallel search and routed slices select their own FO/HO representations. -/
register_option vampire.higherOrder : Bool := {
  defValue := false
  descr := "When parallel and routedSlices are disabled, select native higher-order THF (true) or first-order TFF (false); also controls export-only calls"
}

/-- Keep the checked first-order route available when native higher-order
translation, search or replay fails. Both attempts share the search budget. -/
register_option vampire.higherOrderFallback : Bool := {
  defValue := false
  descr := "Retry failed native higher-order problems with the checked first-order encoding"
}

register_option vampire.higherOrderSliceShare : Nat := {
  defValue := 75
  descr := "Percentage of the remaining search budget for native higher-order search before a first-order retry"
}

register_option vampire.higherOrderSearchRetry : Bool := {
  defValue := true
  descr := "Retry a fast native HO GaveUp with extensionality and heuristic instantiation, using only unspent search time"
}

/-- Constant-specialization saturation can storm on polymorphic premise lists
and consume a whole case budget inside monomorphization. The first-order
monomorphization of the default route is therefore windowed; a blown window
abandons the attempt before the export. The default/sliced tactic first tries
bounded constructor decomposition with one shared additional mono window when
enabled, then retries the original proof natively higher-order with
specialization saturation skipped. This is experimental:
useful dependent and type-polymorphic instances may be lost. Zero disables
both the window and the retry. -/
register_option vampire.monoHeartbeats : Nat := {
  defValue := 0
  descr := "Heartbeat window for first-order monomorphization; on exhaustion the attempt is retried natively higher-order without constant-specialization saturation (0 disables both)"
}

/-- Omitting unsupported local hypotheses weakens the refutation problem.
Every retained premise keeps its checked proof; disable this option to report
unsupported local premises instead. -/
register_option vampire.omitUnsupportedLocalHypotheses : Bool := {
  defValue := true
  descr := "After a monomorphization failure, retry while omitting unrepresentable local hypothesis instances"
}

/-- Shared library that provides the C-backed TPTP parser. Empty selects the
library built with the `tptp_parser` dependency. -/
register_option vampire.tptpParserDynlib : String := {
  defValue := ""
  descr := "Shared library implementing the TPTP parser (empty: the one built with this package)"
}

namespace VampireHammer

initialize registerTraceClass `vampire

end VampireHammer

/-- Sequential time-sliced search over a shared FO/HO preparation, used when
parallel search is disabled. -/
register_option vampire.routedSlices : Bool := {
  defValue := true
  descr := "Time-sliced HO -> FO -> HO schedule over one shared monomorphization: native HO searches its share first, FO then searches its share plus any time HO left unspent, and HO searches again with the alternate strategy only if FO ended early (finite model, GaveUp or another failure, not a timeout) and HO had been prepared (requires a finite timeLimit; ignores monoHeartbeats)"
}

register_option vampire.sliceHoFirst : Nat := {
  defValue := 20
  descr := "Percentage of the search budget for the first native HO slice of routedSlices"
}

register_option vampire.sliceFo : Nat := {
  defValue := 80
  descr := "Percentage of the search budget for the FO slice of routedSlices (plus unspent time of the first HO slice)"
}

register_option vampire.sliceFoBeforeRecovery : Nat := {
  defValue := 10
  descr := "Percentage of the search budget for the first-order slice when the native slice failed on a missing domain; the tactic's inhabitant recovery then retries with the remaining time"
}

register_option vampire.decompositionReserve : Nat := {
  defValue := 30
  descr := "With routedSlices, percentage of the search budget held back from the main attempt for goal decomposition when the goal is one it can split; unspent main time is returned to it"
}

-- Experimental schedules are available to implementation tests only. These
-- keys are deliberately unregistered, so neither set_option nor vampire's
-- inline settings expose them as user options.
namespace VampireHammer.InternalSearch

def staged (options : Lean.Options) : Bool :=
  options.getBool `vampire.internal.stagedSearch false

def routed (options : Lean.Options) : Bool :=
  options.getBool `vampire.internal.routedSearch false

def routeOverride (options : Lean.Options) : String :=
  options.get `vampire.internal.routeOverride ""

def prepareAsync (options : Lean.Options) : Bool :=
  options.getBool `vampire.internal.prepareHigherOrderAsync true

end VampireHammer.InternalSearch

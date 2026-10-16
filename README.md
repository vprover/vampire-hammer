# VampireHammer

VampireHammer is a Lean 4 tactic that uses Vampire to search for proofs and
reconstructs them in Lean. Every successful proof is checked by Lean's kernel.
It supports typed first-order problems and an experimental native higher-order
route.

## Installation

Use Lean 4.34.1 and add this to your `lakefile.lean`:

```lean
require vampire_hammer from git "https://github.com/vprover/vampire-hammer" @ "main"
```

If your project uses `lakefile.toml`, add this instead:

```toml
[[require]]
name = "vampire_hammer"
git = "https://github.com/vprover/vampire-hammer"
rev = "main"
```

Run `lake update` and `lake build`. Git, CMake and a C++17 compiler are
required; Lake builds Vampire and the bundled TPTP parser automatically.
The core library does not require mathlib or Duper. Pin a commit instead of
`main` for reproducible builds.

## Usage

```lean
import VampireHammer

example (p q : α → Prop) (a : α) (h₁ : ∀ x, p x → q x) (h₂ : p a) : q a := by
  vampire [h₁, h₂]
```

Use `vampire [*]` for all local hypotheses. Per-call settings include
`(timeout := 20)`, `(quiet := false)`, `(unfold := [f])` and `(defeq := [f])`.
`(quiet := false)` enables a general success message. If a successful proof
uses automatically added premises, VampireHammer reports their origins and
statements, including on cache hits. Use `(reportFacts := false)` to hide this
report. Unused automatic premises are not reported.

Use `vampire only [h₁, h₂, lemma]` to restrict the tactic to supplied facts.
This disables automatic library lemmas, structure/typeclass laws, constructor
facts and Boolean facts. `vampire only` means `vampire only []`;
`vampire only [*]` explicitly includes local hypotheses. Hypotheses introduced
from the goal, logical inference and definitional reduction remain available.
The same restriction is available with `vampire_export only`.

The default search allowance is 10 seconds per parallel attempt.
Translation and reconstruction also use Lean's heartbeat
budget. See [tactic options](docs/TACTIC_OPTIONS.md) for configuration.

Concurrent search is enabled by default. It monomorphizes once for the
original goal, then races native HO and
checked FO search. When goal decomposition is enabled, a separate attempt
splits the goal and searches its branches alongside the original attempt.
The first successfully replayed proof wins and cancels the other attempts.
Use `(portfolioCores := 4)` to run four workers within each FO Vampire
portfolio; this also works with the sequential tactic schedule.
The independent `portfolioCores` setting defaults to `1` per portfolio.
Use `(parallel := false)` to select the sequential tactic schedule.

Set `vampire.outputPath` to retain the input and prover output, or
`trace.vampire` for diagnostics. Set `vampire.executable` to use another
certificate-emitting Vampire build.

## Further information

- [Examples](Examples/) and [tests](Tests/).
- [Pipeline](docs/PIPELINE_OVERVIEW.md) and [module map](VampireHammer/README.md).
- [Higher-order support](docs/HIGHER_ORDER_SCOPE.md).
- [Benchmarks](benchexec/README.md) and [dependencies](vendor/README.md).
- [Contributor notes](CONTRIBUTING.md).

# Generative AI statement

Large parts of lean reconstruction were generated with the help of AI tools such as (Claude Opus 5.5, GPT-6.1-Sol and GLM 5.3)

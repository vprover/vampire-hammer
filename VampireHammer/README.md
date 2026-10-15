# Module map

Import `VampireHammer` to use the tactics.

| Entry point | Purpose |
| --- | --- |
| [Tactic.lean](Tactic.lean) | Tactic syntax, goal preparation and proof assignment |
| [Options.lean](Options.lean) | Configuration names and defaults |
| [ProofCache.lean](ProofCache.lean) | Bounded session cache of closed, kernel-checked Lean proofs |
| [Export/](Export/) | Premise collection, translation and Vampire invocation |
| [TFF.lean](TFF.lean) | Typed first-order encoding |
| [TSTP.lean](TSTP.lean) | TPTP parser interface |
| [Replay/Decode.lean](Replay/Decode.lean) | Typed proof and certificate decoding |
| [Replay/Steps.lean](Replay/Steps.lean) | Proof DAG reconstruction |
| [Replay/Import.lean](Replay/Import.lean) | Import of the completed proof through lean-auto |
| [Backend/](Backend/README.md) | Individual inference handlers |
| [Clause.lean](Clause.lean) | Clause and AVATAR proof interfaces |
| [Preprocess.lean](Preprocess.lean) | Checked preprocessing |
| [Benchmark/](Benchmark/) | Optional benchmark harnesses |

See the [pipeline overview](../docs/PIPELINE_OVERVIEW.md) for the overall flow and
[reconstruction guide](../docs/RECONSTRUCTION_DESIGN.md) for proof boundaries.

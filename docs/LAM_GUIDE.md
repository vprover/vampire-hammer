# lean-auto representations

VampireHammer uses lean-auto's simply typed term language during translation
and decoding.

| Representation | Purpose |
| --- | --- |
| `Lean.Expr` | Lean expressions and kernel-checkable proofs |
| `LamSort` | Atomic, base and non-dependent function sorts |
| `LamTerm` | Typed symbolic terms, including atoms, binders and application |
| TPTP syntax | Interchange format for Vampire |

Reification records how symbolic atoms correspond to Lean expressions.
The exporter retains that mapping so replay can decode the prover's terms
in the same signature. Bound variables use de Bruijn indices; substitutions
must respect their scope and sorts.

Replay constructs a local Lean proof before one final `Lam2DAAF` import.
For upstream definitions, see `Auto/Embedding/LamBase.lean`,
`Auto/Translation/LamReif.lean` and
`Auto/Translation/Lam2DAtomAsFVar.lean` in the `auto` dependency.
See [reconstruction](RECONSTRUCTION_DESIGN.md) for the project boundaries.

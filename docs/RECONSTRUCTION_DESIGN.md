# Proof reconstruction

Replay converts Vampire's TSTP proof into a typed proof DAG and reconstructs
it in a local Lean signature. It then imports the completed refutation
through lean-auto's `Lam2DAAF` bridge.

| Boundary | Check |
| --- | --- |
| Input facts | Parsed formulas agree with the supplied Lean proofs |
| Fresh symbols | Definitions or witnesses have a checked interpretation |
| Derived nodes | A handler proves the displayed conclusion from its parents |
| Clause transport | Literal positions, substitutions and side conditions agree |
| Final import | The refutation proves the original Lean goal |

Each derived node is a local lemma over parent hypotheses, applied to the
stored parent proofs. Explicit result-type hints keep later steps from
repeatedly expanding the accumulated proof DAG. Clause conversion happens
inside the local lemma.

Regular clauses use ordered literal lists; AVATAR assumptions have separate
set semantics. Unsupported direct inferences may use an isolated `grind`
check. Vampire's reported success alone is never accepted as a proof.

Entry points are [Decode.lean](../VampireHammer/Replay/Decode.lean),
[Steps.lean](../VampireHammer/Replay/Steps.lean),
[Import.lean](../VampireHammer/Replay/Import.lean) and the
[inference backend](../VampireHammer/Backend/README.md).

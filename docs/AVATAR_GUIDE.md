# AVATAR replay

AVATAR splits first-order search into components and combines their results
with a propositional SAT refutation.

Replay stores an AVATAR clause as
`AClause.Holds regular avatar`: the disjunction of the regular literals and
the AVATAR assumptions. Regular literals are ordered and occurrence-sensitive.
AVATAR assumptions have set semantics; transport checks membership in both
directions. Regular-clause permutations require a separate checked step.

Component definitions and split certificates connect the propositional names
to their first-order formulas. SAT conversion checks that mapping, and SAT
refutation uses checked propagation, LRAT reflection or `bv_decide`.

| Implementation | Purpose |
| --- | --- |
| [Clause.lean](../VampireHammer/Clause.lean) | Clause interfaces and transport |
| [Replay/Decode/](../VampireHammer/Replay/Decode/) | Certificate decoding |
| [Backend/Avatar.lean](../VampireHammer/Backend/Avatar.lean) | Component and split rules |
| [Backend/Sat.lean](../VampireHammer/Backend/Sat.lean) | SAT conversion and refutation |

Use `(disableAvatar := true)` to request a first-order proof without AVATAR.
SAT replay limits are listed in the [option reference](TACTIC_OPTIONS.md).

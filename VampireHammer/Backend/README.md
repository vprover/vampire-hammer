# Inference backend

[Dispatch.lean](Dispatch.lean) selects a handler for each decoded Vampire rule.
[../Backend.lean](../Backend.lean) checks its result and stores the proof as a
local lemma over the parent hypotheses. Input facts are checked against their
source proofs. Derived steps without a direct handler can use the checked
`grind` fallback.

| Modules | Purpose |
| --- | --- |
| [Types.lean](Types.lean), [Metadata.lean](Metadata.lean) | Rule inputs and certificate decoding |
| [Instantiation.lean](Instantiation.lean), [HigherOrderTerm.lean](HigherOrderTerm.lean) | Typed parent substitutions |
| [Resolution.lean](Resolution.lean), [Factoring.lean](Factoring.lean) | Resolution and factoring |
| [Equality.lean](Equality.lean), [Rewriting.lean](Rewriting.lean) | Equality inferences and rewriting |
| [CertifiedRewriting.lean](CertifiedRewriting.lean), [Occurrence.lean](Occurrence.lean) | Certificate-directed rewriting |
| [Preprocessing.lean](Preprocessing.lean), [Simplification.lean](Simplification.lean) | Formula preprocessing and simplification |
| [Definitions.lean](Definitions.lean), [Naming.lean](Naming.lean) | Fresh definitions and splitting |
| [HigherOrder.lean](HigherOrder.lean), [HigherOrderBoolean.lean](HigherOrderBoolean.lean), [HigherOrderQuantifier.lean](HigherOrderQuantifier.lean) | Higher-order and Boolean inferences |
| [HigherOrderChoice.lean](HigherOrderChoice.lean), [HigherOrderAxiom.lean](HigherOrderAxiom.lean) | Checked logical operators |
| [Avatar.lean](Avatar.lean), [Sat.lean](Sat.lean) | AVATAR and SAT replay |
| [Common.lean](Common.lean), [Permutation.lean](Permutation.lean) | Clause transport and explicit permutations |
| [Fallback.lean](Fallback.lean) | Generic checked fallback |

To add a rule, decode its metadata, implement its handler and register it in
dispatch. Check the entire conclusion, including side literals and AVATAR
assumptions. Add valid and rejected-certificate cases under
[Tests/Backend](../../Tests/Backend/).

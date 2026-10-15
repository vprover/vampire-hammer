# Higher-order replay certificates

Native higher-order replay requires Vampire's certificate-emitting build,
selected automatically by Lake. Certificates supply substitutions, witnesses
and occurrence information that cannot be inferred safely from a rule name.

| Rule family | Certificate information |
| --- | --- |
| Instantiation and constrained calculus | Typed parent substitutions in `unifier([subs(...)])`; higher-order terms use `$thf(...)` |
| Heuristic instantiation | `quantifier_instance(literal,$thf(term))` |
| Negative extensionality and quantified proxies | Selected literal, checked witness and its dependencies |
| Certified rewriting | Selected literal and rewrite terms; optional `occurrence(n)` |
| Boolean cases | `boolean_case(literal(parent,index),$thf(term),true)` or `false`, with an optional occurrence |
| Flex-flex closure | A supplied common instance, checked to close the clause |
| Choice and extensionality axioms | A certified logical operator and its checked instance |

Occurrence indices are zero-based over typed matching subterms. Scope and
sort checks apply beneath binders. Witness checks include dependency lists;
omitted dependencies must be absent from both the witness value and its type.
Every handler checks the complete child clause.

Real prover outputs are retained under [Tests/testdata/higher-order](../Tests/testdata/higher-order/).
Files named `*.mock.tstp` exercise synthetic certificate cases, including
paths not covered by those real outputs. Raw polymorphic choice syntax
(`@+`/`@@+`) remains unsupported.

See [replay tests](../Tests/HigherOrder/HigherOrderReplayTests.lean),
[pipeline tests](../Tests/HigherOrder/HigherOrderPipelineTests.lean) and
[backend handlers](../VampireHammer/Backend/README.md) for concrete contracts.

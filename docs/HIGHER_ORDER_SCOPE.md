# Higher-order support

Native higher-order export uses simply typed THF for functions, propositions,
curried application and typed lambdas. The default routed schedule tries
higher-order search before first-order search.

To select a single route:

```lean
vampire (routedSlices := false) (higherOrder := true) [*]
```

Set `higherOrderFallback := true` to allow a first-order retry after a failed
native attempt. `vampire_export (higherOrder := true)` selects THF export.

Replay supports certified substitutions, constrained equality inferences,
extensionality, Boolean rules, quantified proxies and selected choice axioms.
Atomic domains require checked inhabitation evidence. `Bool` and `Prop`
remain distinct. Coverage is experimental: unsupported terms or certificates
can prevent reconstruction even when Vampire finds a proof.

See [certificate requirements](VAMPIRE_HO_CERTIFICATES.md),
[higher-order tests](../Tests/HigherOrder/) and [options](TACTIC_OPTIONS.md).

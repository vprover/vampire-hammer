# Dependencies

| Dependency | Source |
| --- | --- |
| lean-auto | Translation fork at `https://github.com/i-am-a-teapot/lean-auto` |
| VampLean | `https://github.com/vprover/vamplean` |
| TPTP parser | Bundled in [tptp_parser/](tptp_parser/README.md) |
| Vampire | Certificate-emitting commit `f88321acd46b9c64c752b800d0adc55441371c4e` from `https://github.com/vprover/vampire` (built with `-DVIRAS=OFF`) |

Lean and dependency revisions are recorded in [lean-toolchain](../lean-toolchain),
[lakefile.lean](../lakefile.lean) and [lake-manifest.json](../lake-manifest.json).
The parser retains its upstream license.

Lake builds Vampire automatically. For an existing prover, use
`lake -R -KbuildVampire=false build` and set `vampire.executable` if the
binary is not on `PATH`. Build settings include `vampireJobs`,
`vampireRepository` and `vampireStatic`. The `vampireRevision` constant in
`lakefile.lean` pins the prover commit.

mathlib is an optional test and benchmark dependency, enabled with `-Kmathlib=true`.

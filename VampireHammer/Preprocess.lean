import VampireHammer.Preprocess.Passes

/-!
Parser-side proof preprocessing.

The live `prepare` entry point runs before `Replay.decodeSteps` and preserves
Vampire's native AC certificates and quantified A-clauses unchanged.

`Preprocess.Passes` retains optional normalization passes for archived
certificates. They rebuild only `Tptp.Data` values, preserve proof parents,
and insert explicit TSTP steps when clause ordering needs a bridge. See
`Preprocess/Passes.lean` for these compatibility operations and
`Tests/Preprocess/PreprocessTests.lean` for their regression coverage.
-/

namespace VampireHammer.Preprocess

open Tptp.Data

/-- Parser-side preparation used by `vampire` before formula decoding.

Current Vampire certificates emit their own `associativity_commutativity`
nodes, so replay receives those proof steps directly rather than synthesizing
clause-order bridges here.  The decoder also recognizes Vampire's native
quantified A-clause spelling, so it need not be rewritten in the parser AST.
The individual compatibility passes above remain available for archived
certificates, but are deliberately not part of this live pipeline. -/
def prepare : Pass := fun proof => pure proof

end VampireHammer.Preprocess

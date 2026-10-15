import Lean
import Tptp

/-!
Parser-AST proof passes and their explicit sequential composition.
-/

namespace VampireHammer.Preprocess

open Tptp.Data

/-- A syntactic proof transformation.  The result is still a parser AST and
has not crossed into the decoder or into Lean metaprogramming. -/
abbrev Pass := TptpFile → Except String TptpFile

/-- Run independent parser-side transformations in their listed order. -/
def run (passes : List Pass) (proof : TptpFile) : Except String TptpFile :=
  passes.foldlM (fun current pass => pass current) proof

end VampireHammer.Preprocess

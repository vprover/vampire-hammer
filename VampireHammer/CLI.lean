import VampireHammer.TSTP
import VampireHammer.Preprocess
import VampireHammer.TptpPrinter

namespace VampireHammer

private def usage : IO UInt32 := do
  IO.eprintln "usage: vampire-preprocess <input.tstp> <output.tstp> [parser-dynlib]"
  IO.eprintln "default parser library: the one built with this package"
  pure 1

/-- Standalone entry point for parser-side proof normalization.  It does not
invoke Vampire, construct Lean expressions, or run reconstruction rules. -/
def main (arguments : List String) : IO UInt32 := do
  -- `lake exe name -- ...` forwards the separator on some Lake versions.
  -- Accept both that conventional spelling and direct executable arguments.
  let arguments := match arguments with
    | "--" :: rest => rest
    | rest => rest
  let (input, output, parserDynlib) ← match arguments with
    | [input, output] => pure (input, output, "")
    | [input, output, parserDynlib] => pure (input, output, parserDynlib)
    | _ => return ← usage
  -- The default parser library is located through the Lean search path,
  -- which `lake exe` provides in `LEAN_PATH`.
  Lean.initSearchPath (← Lean.findSysroot)
  match ← parseVampireTSTP parserDynlib input with
  | .error message =>
    IO.eprintln s!"could not parse `{input}`: {message}"
    pure 2
  | .ok proof =>
    match Preprocess.prepare proof with
    | .error message =>
      IO.eprintln s!"could not preprocess `{input}`: {message}"
      pure 3
    | .ok proof =>
      match TptpPrinter.render proof with
      | .error message =>
        IO.eprintln s!"could not render transformed proof: {message}"
        pure 4
      | .ok text =>
        IO.FS.writeFile output text
        let .mk inputs := proof
        IO.println s!"wrote {inputs.length} transformed TPTP items to `{output}`"
        pure 0

end VampireHammer

/-- Lake executable entry point. The implementation remains namespaced so it
can also be invoked from a Lean test without shelling out. -/
def main (arguments : List String) : IO UInt32 := VampireHammer.main arguments

import Tptp

def main (args : List String) : IO UInt32 := do
  let [filename] := args
    | IO.eprintln "usage: ParserCheck FILE"
      return 1

  match ← Tptp.Parser.parseFile filename with
  | .ok parsed =>
      IO.println "Parser result: OK"
      IO.println (repr parsed)

      return 0
  | .error message =>
      IO.eprintln s!"Parser result: ERROR: {message}"
      return 2

import Tptp.Data
import Tptp.Parser

def usage : String :=
  "USAGE
  tptp PATH
"

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if args.length != 1 then
    stderr.putStrLn usage
    return 1

  let res ← Tptp.Parser.parseFile args[0]!

  match res with
  | .ok _res =>
    stdout.putStrLn "OK"
    return 0
  | .error e =>
    stdout.putStrLn "FAIL"
    stderr.putStrLn e
    return 2

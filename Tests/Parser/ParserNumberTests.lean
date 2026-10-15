import VampireHammer.TSTP
import VampireHammer.TptpPrinter

open VampireHammer Tptp.Data

private def numbers : TptpFile → Except String (List String)
  | .mk inputs => inputs.mapM fun
    | .annotatedFormula (.tffAnnotated (.mk _ _ _
        (.sourceOptionalInfo (.dagSource (.inferenceRecord
          (.mk _ (.mk (.generalTerms (.mk (.generalData (.number value)) []))) _))) _))) =>
      pure (reprStr value)
    | _ => throw "expected a single numeric inference annotation"

#eval show IO Unit from do
  let cases : List (String × Number) := [
    ("1.25E-3", .real (.mk 125 (-5))),
    ("-0.125E+4", .real (.mk (-125) 1)),
    ("123.4500e+02", .real (.mk 1234500 (-2))),
    ("6.0E3", .real (.mk 60 2)),
    ("0.0E-9", .real (.mk 0 (-10))),
    ("12E+34", .real (.mk 12 34)),
    ("+7E-8", .real (.mk 7 (-8))),
    ("4.25", .real (.mk 425 (-2))),
    ("-4.25", .real (.mk (-425) (-2))),
    ("123456789012345678901234567890.5E-123456789012345678901234567890",
      .real (.mk 1234567890123456789012345678905 (-123456789012345678901234567891))),
    ("-4/7", .rational (.mk (-4) 7)),
    ("+4/7", .rational (.mk 4 7)),
    ("+17", .integer (.mk 17)),
    ("123456789012345678901234567890", .integer (.mk 123456789012345678901234567890))]
  let directory : System.FilePath := "artifacts/parser-numbers"
  IO.FS.createDirAll directory
  let path := directory / "input.tstp"
  let text := String.join <| cases.zipIdx.map fun ((literal, _), index) =>
    s!"tff(n{index},plain,$true,inference(test,[{literal}],[])).\n"
  IO.FS.writeFile path text
  let library := ""
  let original ← IO.ofExcept (← parseVampireTSTP library path.toString)
  let expected := cases.map (reprStr ∘ Prod.snd)
  unless (← IO.ofExcept (numbers original)) == expected do
    throw <| IO.userError s!"incorrect numeric values: {← IO.ofExcept (numbers original)}"
  let rendered ← IO.ofExcept (TptpPrinter.render original)
  let output := directory / "output.tstp"
  IO.FS.writeFile output rendered
  let roundTrip ← IO.ofExcept (← parseVampireTSTP library output.toString)
  unless (← IO.ofExcept (numbers roundTrip)) == expected do
    throw <| IO.userError "printing changed a numeric annotation's value"
  IO.println "Parser numbers: signed decimals, exponents, rationals, and arbitrary-precision values passed"

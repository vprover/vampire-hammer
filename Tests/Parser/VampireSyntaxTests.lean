import VampireHammer.TSTP

open VampireHammer

/-! Exercise the C entry points directly: none of these cases may depend on
rewriting the input in the hammer's Lean adapter. Compare complete ASTs so
grouping, metadata and mixed record dialects retain their meaning. -/
#eval show IO Unit from do
  let _ ← IO.ofExcept (← parseVampireTSTPText "" "") -- load the C library
  let cases := [
    ("thf(f,plain,((=\n@ a) @ a)).", "thf(f,plain,(((=) @ a) @ a))."),
    ("tff(f,plain,(~ f(X,b) = 'c' => p)).",
      "tff(f,plain,(~ (f(X,b) = 'c') => p))."),
    ("tff(f,plain,(~ a != b => p)).", "tff(f,plain,(~ (a != b) => p))."),
    ("thf(f,plain,(~ (f @ X) = a => p)).",
      "thf(f,plain,(~ ((f @ X) = a) => p))."),
    ("fof(f,plain,($ite((p & q),a,$ite(q,b,a)) = a)).",
      "tff(f,plain,($ite((p & q),a,$ite(q,b,a)) = a))."),
    -- Promote only the conditional record, never its FOF neighbours.
    ("fof(a,plain,p).\nfof (b,plain,($ite(p,a,b) = a)).\nfof(c,plain,q).",
      "fof(a,plain,p).\ntff(b,plain,($ite(p,a,b) = a)).\nfof(c,plain,q)."),
    -- Comments, quotes, and embedded annotation formulas are not record syntax.
    ("/* $ite(p,a,b) */ fof(f,plain,p,file('$ite(p,a,b)','(= @ a)')).",
      "fof(f,plain,p,file('$ite(p,a,b)','(= @ a)'))."),
    ("fof(f,plain,p,inference(test,[$thf($ite(p,a,b))],[])).",
      "fof(f,plain,p,inference(test,[$thf($ite(p,a,b))],[]))."),
    ("thf(f,plain,p,inference(test,[$thf(= @ a)],[])).",
      "thf(f,plain,p,inference(test,[$thf((=) @ a)],[])).")
  ]
  let directory : System.FilePath := "artifacts/parser-vampire-syntax"
  IO.FS.createDirAll directory
  for ((raw, canonical), i) in cases.zipIdx do
    let parsed ← IO.ofExcept (← Tptp.Parser.parseString raw)
    let expected ← IO.ofExcept (← Tptp.Parser.parseString canonical)
    unless reprStr parsed == reprStr expected do
      throw <| IO.userError s!"Vampire syntax case {i} changed the AST"
    let path := directory / s!"case-{i}.p"
    IO.FS.writeFile path raw
    let fromFile ← IO.ofExcept (← Tptp.Parser.parseFile path.toString)
    unless reprStr fromFile == reprStr expected do
      throw <| IO.userError s!"Vampire syntax case {i} differs in file parsing"
  -- Grow the FOF lookahead buffer, including quantified comma-separated vars.
  let terms := String.intercalate "," (List.replicate 200 "X")
  let long := s!"fof(f,plain,(! [X,Y] : (p({terms}) => q(Y))))."
  let _ ← IO.ofExcept (← Tptp.Parser.parseString long)
  -- Abandon queued tokens on failure, then parse another independent record.
  for bad in ["fof(f,plain,($ite(p,a,b) = )).", "fof(f,plain,p(unfinished"] do
    if (← Tptp.Parser.parseString bad).isOk then
      throw <| IO.userError "accepted malformed FOF input"
    let _ ← IO.ofExcept (← Tptp.Parser.parseString "fof(ok,plain,p).")
  IO.println "Vampire syntax: direct C file/text parsing and AST preservation passed"

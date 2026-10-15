import VampireHammer.TSTP
import VampireHammer.TptpPrinter

open VampireHammer

private def certificates : Tptp.Data.TptpFile → Except String (List String)
  | .mk inputs => inputs.mapM fun
    | .annotatedFormula (.tffAnnotated (.mk name role _ annotations)) =>
      pure (reprStr (name, role, annotations))
    | _ => throw "expected TFF proof items"

/-! The standalone writer must produce parseable TF0 and preserve inference
annotations, including colon terms, lists, and quoted source names. Its explicit
parentheses change the grammar AST, so compare certificate records separately. -/
#eval show IO Unit from do
  let library := ""
  let directory : System.FilePath := "artifacts/printer-tests"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "colon.tstp")
    "tff(c,plain,p,inference(test,[status(thm),binding(X : a),detail('quoted name')],[parent])).\n"
  IO.FS.writeFile (directory / "metadata.tstp") <| String.join [
    "tff(`Entry,plain-[label('quoted name'),weight(4/7,1.25E-3)],p,",
    "inference(test,[tag(`Marker)],[parent : [selected(1)],",
    "inference(nested,[],[file('input',original)]),",
    "introduced(definition,[new_symbols(definition,[fresh])],[]),",
    "theory(equality,[status(thm)]),creator(tool,[],[]),unknown,",
    "[file('input'),theory(equality)]]),[extra(42)]).\n"]
  for fixture in #["preprocess-resolution.tstp", "preprocess-resolution-ordered.tstp",
      "preprocess-resolution-negative-first-ordered.tstp", "colon.tstp", "metadata.tstp",
      "preprocess-forward-subsumption.tstp", "preprocess-equality-resolution.tstp",
      "naming-rules.tstp", "rewriting-certificates.tstp", "nested-a-clause.tstp",
      "shared-forward-parents.tstp"] do
    let source := if fixture == "colon.tstp" || fixture == "metadata.tstp" then
      directory / fixture else System.FilePath.mk "Tests/testdata" / fixture
    let original ← IO.ofExcept (← parseVampireTSTP library source.toString)
    let text ← IO.ofExcept (TptpPrinter.render original)
    let path := directory / fixture
    IO.FS.writeFile path text
    let parsed ← IO.ofExcept (← parseVampireTSTP library path.toString)
    unless (← IO.ofExcept (certificates parsed)) == (← IO.ofExcept (certificates original)) do
      throw <| IO.userError s!"TPTP writer changed certificates in {fixture}"
  -- Embedded formulas remain unsupported; their metadata must never vanish.
  IO.FS.writeFile (directory / "unsupported.tstp")
    "tff(c,plain,p,inference(test,[$fof(p)],[])).\n"
  let unsupported ← IO.ofExcept (← parseVampireTSTP library (directory / "unsupported.tstp").toString)
  match TptpPrinter.render unsupported with
  | .ok _ => throw <| IO.userError "silently dropped an unsupported embedded formula"
  | .error message => unless message.contains "embedded" do
      throw <| IO.userError s!"unexpected unsupported metadata diagnostic: {message}"
  IO.println "TPTP writer: eleven fixtures preserved sources, parent details, roles, and optional metadata"

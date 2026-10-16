import Tptp
import Lean.LoadDynlib
import Lean.Util.Path
import Std.Sync.Mutex
import Std.Data.HashSet

namespace VampireHammer

private initialize parserReady : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- Only dynamic-library registration is process-wide. Record individual
successful loads so a failed load can be retried without registering duplicate
symbols. Once ready, subsequent calls bypass this lock entirely. -/
private initialize libraryLoader : Std.Mutex (Std.HashSet System.FilePath) ←
  Std.Mutex.new {}

/-- Load the C implementation behind the workspace's existing TPTP parser.
The parser itself owns independent scanner and parse contexts per call. -/
private def loadParser (dynlibPath : System.FilePath) : IO Unit := do
  let path ← IO.FS.realPath dynlibPath
  let checkPath (loaded : System.FilePath) : IO Unit := do
    unless loaded == path do
      throw <| IO.userError s!"TPTP parser already loaded from {loaded}; cannot replace it with {path}"
  if let some loaded ← parserReady.get then
    checkPath loaded
    return
  libraryLoader.atomically do
    -- Another caller may have completed registration while we waited.
    if let some loaded ← parserReady.get then
      checkPath loaded
      return
    let some directory := path.parent
      | throw <| IO.userError s!"TPTP parser library has no parent directory: {path}"
    -- The C parser calls constructors exported by `tptp_data`. Loading the
    -- data library first makes those symbols available to the interpreter.
    -- This Lean module supplies the interpreter wrapper for the external
    -- declaration `Tptp.CParser.parseFile`.
    for library in #[directory / "libtptp__parser_tptp__data.so", path,
        directory / "libtptp__parser_tptp__parser.so"] do
      unless (← get).contains library do
        Lean.loadDynlib library
        modify (·.insert library)
    parserReady.set (some path)

/-- The build directory of the package providing `module`, found from its
`.olean` on the Lean search path (`<package>/.lake/build/lib/lean/...`). -/
private def packageBuildDir (module : Lean.Name) : IO System.FilePath := do
  let olean ← Lean.findOLean module
  let some build := olean.parent >>= (·.parent) >>= (·.parent)
    | throw <| IO.userError s!"unexpected location of {module}: {olean}"
  return build

/-- The C parser library built alongside the `Tptp` modules. -/
def defaultParserDynlib : IO System.FilePath := do
  let extension := if System.Platform.isWindows then "dll"
    else if System.Platform.isOSX then "dylib" else "so"
  return (← packageBuildDir `Tptp) / "lib" / s!"libtptp_cparser.{extension}"

/-- The Vampire binary built by this package's `vampire` target, if present;
otherwise `vampire` from `PATH`. -/
def defaultVampireExecutable : IO String := do
  try
    let some lakeDir := (← packageBuildDir `VampireHammer).parent | return "vampire"
    let executable := lakeDir / "vampire" / "build" / "vampire"
    if ← executable.pathExists then return executable.toString
  catch _ => pure ()
  return "vampire"

/-- Parse a raw Vampire TSTP output file. Vampire's `%` status and statistics
comments are valid TPTP comments, so the whole stdout file is supplied intact.
Concurrent parses use independent C scanner buffers, errors, and results. -/
def parseVampireTSTP (dynlibPath path : String) : IO (Except String Tptp.Data.TptpFile) :=
  do
    -- An empty path selects the library built with this package.
    loadParser (← if dynlibPath.isEmpty then defaultParserDynlib else pure dynlibPath)
    -- An unreadable file is a parse failure, as for the parser's own reader.
    let text ← try IO.FS.readFile path
      catch error => return .error s!"cannot read {path}: {error}"
    Tptp.Parser.parseString text

/-- Parse raw Vampire TSTP output held in memory, such as captured stdout. -/
def parseVampireTSTPText (dynlibPath text : String) : IO (Except String Tptp.Data.TptpFile) := do
  loadParser (← if dynlibPath.isEmpty then defaultParserDynlib else pure dynlibPath)
  Tptp.Parser.parseString text

end VampireHammer

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

/-- Vampire can print a partially applied equality as `(= @ X)`, while the
TPTP grammar requires the connective value to be parenthesized: `((=) @ X)`.
Only this head position is rewritten, preserving quoted names and comments. -/
private def parenthesizeEqualityHeads (text : String) : String := Id.run do
  let chars := text.toList.toArray
  let mut output := ""
  let mut quote : Option Char := none
  let mut escaped := false
  let mut lineComment := false
  let mut blockComment := false
  let mut previous := ' '
  let mut syntaxPrevious := ' '
  for i in [:chars.size] do
    let c := chars[i]!
    let next := chars[i+1]?.getD ' '
    if lineComment then
      if c == '\n' then lineComment := false
    else if blockComment then
      if previous == '*' && c == '/' then blockComment := false
    else if let some delimiter := quote then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == delimiter then quote := none
    else if c == '%' then lineComment := true
    else if c == '/' && next == '*' then blockComment := true
    else if c == '\'' || c == '"' then
      quote := some c
      syntaxPrevious := c
    else
      if c == '=' && syntaxPrevious == '(' then
        let mut j := i + 1
        while j < chars.size && chars[j]!.isWhitespace do j := j + 1
        if chars[j]?.getD ' ' == '@' then
          output := output ++ "(=)"
          syntaxPrevious := c
          previous := c
          continue
      if !c.isWhitespace then syntaxPrevious := c
    output := output.push c
    previous := c
  return output

/-- Vampire can print FOOL in `fof` records, although formula arguments of
`$ite` belong to the extended typed grammar. Read those records as TFF; symbol
types still come from the checked problem signature. Quotes/comments and
embedded `$fof` annotations are preserved. -/
private def foolFormulaRecords (text : String) : String := Id.run do
  let chars := text.toList.toArray
  let mut output := ""
  let mut quote : Option Char := none
  let mut escaped := false
  let mut lineComment := false
  let mut blockComment := false
  let mut depth := 0
  let mut hasConditional := false
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    let next := chars[i+1]?.getD ' '
    if lineComment then
      if c == '\n' then lineComment := false
    else if blockComment then
      if c == '*' && next == '/' then
        output := output ++ "*/"
        i := i + 2
        blockComment := false
        continue
    else if let some delimiter := quote then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == delimiter then quote := none
    else if c == '%' then lineComment := true
    else if c == '/' && next == '*' then blockComment := true
    else if c == '\'' || c == '"' then quote := some c
    else
      if c == '$' && next == 'i' && chars[i+2]? == some 't' && chars[i+3]? == some 'e' then
        let mut after := i + 4
        while chars[after]?.any Char.isWhitespace do after := after + 1
        if chars[after]? == some '(' then hasConditional := true
      if depth == 0 && c == 'f' && next == 'o' && chars[i+2]? == some 'f' then
        let mut after := i + 3
        while chars[after]?.any Char.isWhitespace do after := after + 1
        if chars[after]? == some '(' then
          output := output ++ "tff"
          i := i + 3
          continue
      if c == '(' then depth := depth + 1
      else if c == ')' then depth := depth - 1
    output := output.push c
    i := i + 1
  return if hasConditional then output else text

/-- Vampire prints a negated equation as `~ a = b`, but TPTP's `~` applies to a
unitary formula only: write `~ (a = b)`. Each operand is a name or variable,
optionally applied to a parenthesized argument list. Quotes and comments are
preserved; only this pattern outside them is rewritten. -/
private def parenthesizeNegatedEquations (text : String) : String := Id.run do
  let chars := text.toList.toArray
  let isWord (c : Char) := c.isAlphanum || c == '_' || c == '$'
  -- The end of an operand starting at `i`, or `none`.
  let operand (i : Nat) : Option Nat := Id.run do
    let mut j := i
    while j < chars.size && isWord chars[j]! do j := j + 1
    if j == i then return none
    if chars[j]? == some '(' then
      let mut depth := 0
      while j < chars.size do
        if chars[j]! == '(' then depth := depth + 1
        else if chars[j]! == ')' then
          depth := depth - 1
          if depth == 0 then return some (j + 1)
        else if chars[j]! == '\'' || chars[j]! == '"' then return none
        j := j + 1
      return none
    return some j
  let skipSpaces (i : Nat) : Nat := Id.run do
    let mut j := i
    while j < chars.size && chars[j]! == ' ' do j := j + 1
    return j
  let mut output := ""
  let mut quote : Option Char := none
  let mut escaped := false
  let mut lineComment := false
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if lineComment then
      if c == '\n' then lineComment := false
    else if let some delimiter := quote then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == delimiter then quote := none
    else if c == '%' then lineComment := true
    else if c == '\'' || c == '"' then quote := some c
    else if c == '~' && chars[i+1]? != some '|' && chars[i+1]? != some '&' then
      let start := skipSpaces (i + 1)
      if let some leftEnd := operand start then
        let afterLeft := skipSpaces leftEnd
        let negated := chars[afterLeft]? == some '!' && chars[afterLeft + 1]? == some '='
        if chars[afterLeft]? == some '=' || negated then
          let rightStart := skipSpaces (afterLeft + if negated then 2 else 1)
          if let some rightEnd := operand rightStart then
            let equation := String.mk (chars.extract start rightEnd).toList
            output := output ++ "~ (" ++ equation ++ ")"
            i := rightEnd
            continue
    output := output.push c
    i := i + 1
  return output

private def parseCompatibleText (text : String) : IO (Except String Tptp.Data.TptpFile) := do
  let text := foolFormulaRecords text
  let result ← Tptp.Parser.parseString text
  if result.isOk then return result
  let normalized := parenthesizeNegatedEquations (parenthesizeEqualityHeads text)
  if normalized == text then return result
  Tptp.Parser.parseString normalized

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
    parseCompatibleText text

/-- Parse raw Vampire TSTP output held in memory, such as captured stdout. -/
def parseVampireTSTPText (dynlibPath text : String) : IO (Except String Tptp.Data.TptpFile) := do
  loadParser (← if dynlibPath.isEmpty then defaultParserDynlib else pure dynlibPath)
  parseCompatibleText text

end VampireHammer

import Data
import CParser

namespace Tptp.Parser

def parseFile (filename : String) : IO <| Except String Tptp.Data.TptpFile :=
  Tptp.CParser.parseFile filename |>.toIO'

/-- Parse TPTP text that is already in memory. -/
def parseString (text : String) : IO <| Except String Tptp.Data.TptpFile :=
  Tptp.CParser.parseString text |>.toIO'

end Tptp.Parser

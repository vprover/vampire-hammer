import Data

namespace Tptp.CParser

@[extern "Tptp_cparse_parse_file"]
opaque parseFile (filename : String) : EIO String Tptp.Data.TptpFile

@[extern "Tptp_cparse_parse_string"]
opaque parseString (text : @& String) : EIO String Tptp.Data.TptpFile

end Tptp.CParser

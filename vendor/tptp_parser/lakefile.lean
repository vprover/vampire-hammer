import Lake
open Lake DSL

package tptp_parser where
  precompileModules := true

lean_lib tptp_data where
  srcDir := "tptp_data"
  roots := #[`Data, `Export]
  moreLeanArgs := #["-DmaxHeartbeats=1000000"]

input_file cparser_parser.tab.c where
  path := "cparser" / "parser.tab.c"
  text := true

input_file cparser_parser.tab.h where
  path := "cparser" / "parser.tab.h"
  text := true

input_file cparser_extern_defs.h where
  path := "cparser" / "extern_defs.h"
  text := true

target cparser_parser.tab.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "cparser" / "parser.tab.o"
  let srcJob ← cparser_parser.tab.c.fetch
  let headers := (← cparser_parser.tab.h.fetch).mix (← cparser_extern_defs.h.fetch)
  let srcJob := srcJob.zipWith (fun path _ => path) headers
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
  ]
  let traceArgs := #[
    "-fPIC",
  ]
  buildO oFile srcJob weakArgs traceArgs

input_file cparser_lex.yy.c where
  path := "cparser" / "lex.yy.c"
  text := true

target cparser_lex.yy.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "cparser" / "lex.yy.o"
  let srcJob ← cparser_lex.yy.c.fetch
  let srcJob := srcJob.zipWith (fun path _ => path) (← cparser_parser.tab.h.fetch)
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
  ]
  let traceArgs := #[
    "-fPIC",
  ]
  buildO oFile srcJob weakArgs traceArgs

input_file cparser_bridge.c where
  path := "cparser" / "bridge.c"
  text := true

target cparser_bridge.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "cparser" / "bridge.o"
  let srcJob ← cparser_bridge.c.fetch
  let headers := (← cparser_parser.tab.h.fetch).mix (← cparser_extern_defs.h.fetch)
  let srcJob := srcJob.zipWith (fun path _ => path) headers
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-pthread"]

target libtptp_cparser pkg : Dynlib := do
  let libName := "tptp_cparser"
  let libFile := pkg.sharedLibDir / (nameToSharedLib libName)
  let linkObjs := #[
    ← cparser_lex.yy.o.fetch,
    ← cparser_parser.tab.o.fetch,
    ← cparser_bridge.o.fetch,
  ]
  let linkLibs := #[
    ← (← tptp_data.get).shared.fetch
  ]
  let weakArgs := #[
    "-pthread",
    "-I", (← getLeanIncludeDir).toString,
    "-L", (← getLeanLibDir).toString,
    "-lInit_shared",
    "-lleanshared_2",
    "-lleanshared_1",
    "-lleanshared",
    s!"-Wl,-rpath,{← getLeanLibDir}",
    s!"-Wl,-rpath,{pkg.buildDir}/lib",
  ]
  -- Link the C bridge against Lean's shared libraries explicitly above.
  -- Lean's bundled compiler flags select its own sysroot, libc++ and lld;
  -- they are incompatible with the external C++ driver used here.
  -- Compiler environments (e.g. micromamba) select a driver through CXX;
  -- the unprefixed system c++ may not find their linker or sysroot.
  let linker := (← IO.getEnv "CXX").getD "c++"
  buildSharedLib libName libFile linkObjs linkLibs weakArgs #[] (linker := linker)

lean_lib tptp_parser where
  srcDir := "tptp_parser"
  roots := #[`Parser, `CParser]
  moreLinkLibs := #[libtptp_cparser]

@[default_target]
lean_lib TptpParser where
  srcDir := "."
  roots := #[`Tptp]
  needs := #[tptp_data, tptp_parser]
  moreLinkLibs := #[libtptp_cparser]

lean_exe parserCheck where
  root := `ParserCheck
  moreLinkLibs := #[libtptp_cparser]

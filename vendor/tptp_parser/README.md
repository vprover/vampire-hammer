# TPTP parser

Lean data types and a C-backed parser for TPTP. Build with `lake build`;
a C/C++ toolchain is required. `Tptp.Parser.parseFile` uses an independent
scanner and parser context for each call.

The generated C sources are checked in. After editing the grammar or scanner,
install Flex and Bison and run from this directory:

```sh
make -C cparser
lake build
```

When embedding the parser, load its `libtptp_cparser` shared library.
VampireHammer configures this automatically.

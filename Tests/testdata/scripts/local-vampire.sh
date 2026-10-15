#!/bin/sh
set -eu

# Use the replay-enabled Vampire built by Lake by default.
# The regression runner forwards its explicit --vampire choice through this
# variable; fixture scripts continue to use their own configured executables.
exec "${VAMPIRE_BIN:-.lake/vampire/build/vampire}" "$@"

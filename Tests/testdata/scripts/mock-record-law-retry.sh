#!/bin/sh
set -eu
state=artifacts/record-law-retry.calls
arguments=artifacts/record-law-retry.args
printf 'CALL\n' >> "$arguments"
printf '%s\n' "$@" >> "$arguments"
if [ ! -e "$state" ]; then
  printf 'first\n' > "$state"
  cat > /dev/null
  printf '%% SZS status Satisfiable\n'
  exit 0
fi
printf 'second\n' >> "$state"
exec "${VAMPIRE_BIN:-.lake/vampire/build/vampire}" "$@"

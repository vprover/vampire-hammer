#!/bin/sh
# Print the recorded Vampire output named by `--decode <fixture>`, so one
# script serves every fixture: tests select it with `vampire.strategy`.
set -eu
fixture=""
while [ $# -gt 0 ]; do
  if [ "$1" = "--decode" ]; then
    fixture="$2"
    shift
  fi
  shift
done
# Drain the exported problem first: exiting before reading it would race with
# the hammer's write to stdin (broken pipe).
cat > /dev/null
cat "$(dirname "$0")/../$fixture.tstp"

#!/bin/sh
set -eu
# Keep the actual argv in TPTP comments so the capture/replay path can check it.
printf '%% Argument: %s\n' "$@"
cat "$(dirname "$0")/../equality-resolution.tstp"

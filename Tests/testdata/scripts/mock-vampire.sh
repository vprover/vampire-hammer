#!/bin/sh
set -eu
# The only argument is the destination. The problem arrives on stdin.
test "$#" -eq 1
mkdir -p "$(dirname "$1")"
cat > "$1"

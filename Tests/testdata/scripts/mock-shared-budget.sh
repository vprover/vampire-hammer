#!/bin/sh
set -eu
previous=
for argument in "$@"; do
  if [ "$previous" = --time_limit ]; then
    printf '%s\n' "$argument" >> artifacts/goal-decomposition/shared-budget.calls
  fi
  previous="$argument"
done
cat > /dev/null
sleep 1
printf '%% SZS status Satisfiable\n'

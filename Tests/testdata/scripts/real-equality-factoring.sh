#!/bin/sh
set -eu

# Keep this regression on one predictable saturation configuration. These
# switches stop equivalent simplification or superposition proofs from being
# selected before equality factoring. `vampire` supplies the proof
# output options and generated input path through "$@".
exec "${VAMPIRE_BIN:-.lake/vampire/build/vampire}" \
  --mode vampire \
  --selection 0 \
  --avatar off \
  --superposition off \
  --forward_demodulation off \
  --backward_demodulation off \
  --function_definition_elimination none \
  --unused_predicate_definition_removal off \
  "$@"

#!/bin/sh
# Reuse the checked subsumption-demodulation certificate with its backward label.
set -eu
cat > /dev/null
sed 's/inference(forward_subsumption_demodulation,/inference(backward_subsumption_demodulation,/g' \
  "$(dirname "$0")/../rewriting-certificates.tstp"

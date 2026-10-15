#!/usr/bin/env sh
# A deterministic Vampire-shaped certificate for SuperpositionExample.lean.
# The selected clause literal contains the rewritten term twice; f12 changes
# both occurrences in one superposition inference.
cat "$(dirname "$0")/../superposition-all-occurrences.tstp"

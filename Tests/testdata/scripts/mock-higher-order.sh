#!/bin/sh
set -eu
# The corresponding test exports p=t_a0, a=t_a1, b=t_a2. Source-fact
# verification rejects the fixture if that signature or fact order changes.
cat "$(dirname "$0")/../higher-order/lambda.pipeline.mock.tstp"

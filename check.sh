#!/bin/sh
# The gate: every law in LAWS.bend must be proven in PROOF.bend,
# first by bend2, then again by the Lean-proven BendTT kernel.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY=1
bend PROOF.bend --check-only
bend PROOF.bend --verdict

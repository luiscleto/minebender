#!/bin/sh
# The gate: every law in LAWS.bend must be proven in PROOF.bend, first by
# bend2, then again by the Lean-proven BendTT kernel (--verdict needs Lean
# v4.34.0, installed with elan into ~/.elan).
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY=1
export PATH="$HOME/.elan/bin:$PATH"
bend examples.bend --check-only 2>&1 | grep -q 'ALL PROOFS CHECK\|TODOs' || { bend examples.bend --check-only; exit 1; }
bend ui.bend --check-only
bend PROOF.bend --check-only
bend PROOF.bend --verdict

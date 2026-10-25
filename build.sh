#!/bin/sh
# Builds the web page: docs/ui.mjs is the game, compiled from ui.bend.
# docs/index.html and docs/worker.js are hand-written and stay thin.
set -e
cd "$(dirname "$0")"
export BEND_NO_TELEMETRY=1
bend ui.bend -o docs/ui.mjs

#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
bash scripts/rebuild.sh
source scripts/env.sh
scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o build/ChordComb2Audit.olean src/ChordComb2Audit.lean
scripts/capped.sh "$LEAN_BIN/leanchecker" ChordComb2Audit

#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
m=$1
echo "MODULE=$m"
scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean"
scripts/capped.sh "$LEAN_BIN/leanchecker" "$m"
if [[ -f "$ROOT/STOP" ]]; then exit 75; fi

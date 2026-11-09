#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
m=$1
echo "MODULE=$m"
scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean" || true
grep -E "^EXIT|error|warning" logs/$(ls -t logs | head -1) | head -30

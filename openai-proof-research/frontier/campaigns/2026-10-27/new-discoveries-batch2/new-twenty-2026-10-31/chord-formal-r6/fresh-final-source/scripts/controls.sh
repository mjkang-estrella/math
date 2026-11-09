#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
for f in controls/*.lean; do
  if scripts/capped.sh "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true "$f"; then
    echo "NEGATIVE CONTROL INCORRECTLY PASSED: $f"; exit 1
  fi
done

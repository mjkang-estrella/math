#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
for f in UlasOdd5NegativeColour UlasOdd5NegativeFifteen UlasOdd5NegativeEven; do
  log="$f-$(date +%s%N)"
  if bash "$L/scripts/run.sh" "$log" lean -j1 -M3500 -DwarningAsError=true "$L/scripts/$f.lean"; then
    echo "Unexpected success: $f"; exit 1
  fi
  rg -q 'Type mismatch|type mismatch' "$L/logs/$log.log"
done
echo 'All three round-5 negative controls rejected with type mismatch.'

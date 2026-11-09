#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
for f in UlasEven5NegativeEven UlasEven5NegativeUnconditional UlasEven5NegativeRho UlasEven5NegativeFifteen UlasEven5NegativeColour; do
  log="$f-$(date +%s%N)"
  if bash "$L/scripts/run.sh" "$log" lean -j1 -M3500 -DwarningAsError=true "$L/scripts/$f.lean"; then
    echo "Unexpected success: $f"; exit 1
  fi
  rg -q 'Type mismatch|type mismatch' "$L/logs/$log.log"
done
echo 'All five negative controls rejected with type mismatch.'

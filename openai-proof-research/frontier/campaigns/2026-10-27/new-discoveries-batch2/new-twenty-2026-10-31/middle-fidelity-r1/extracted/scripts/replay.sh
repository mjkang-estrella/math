#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
SRC=${1:-$LANE}
OUT=${2:-$LANE/build}
mkdir -p "$OUT"
export LEAN_PATH="$OUT:${LEAN_PATH}"
cd "$SRC"
for module in MiddleBase MiddleSmall MiddleWitness MiddleFinal MiddleAudit; do
  "$LANE/scripts/run.sh" "rebuild-$module" "$LEAN" -j1 -M3500 -DwarningAsError=true -o "$OUT/$module.olean" "$module.lean"
  "$LANE/scripts/run.sh" "leanchecker-$module" "${LEAN%/lean}/leanchecker" "$module"
done
for module in NegativeValue NegativeAdjacency NegativeConnected; do
  if "$LANE/scripts/run.sh" "negative-$module" "$LEAN" -j1 -M3500 -DwarningAsError=true "$module.lean"; then
    echo "NEGATIVE CONTROL UNEXPECTEDLY PASSED: $module"
    exit 1
  fi
done
"$LANE/scripts/run.sh" regression python3 -I "$LANE/scripts/regression.py"
echo REPLAY_PASS

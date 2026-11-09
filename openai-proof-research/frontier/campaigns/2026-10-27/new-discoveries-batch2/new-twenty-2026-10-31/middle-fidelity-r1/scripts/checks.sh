#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$LANE/extracted"
for module in MiddleBase MiddleSmall MiddleWitness MiddleFinal MiddleAudit; do
 "$LANE/scripts/run.sh" "compile-$module" "$LEAN" -j1 -M3500 -DwarningAsError=true -o "$LANE/build/$module.olean" "$module.lean"
 "$LANE/scripts/run.sh" "check-$module" "${LEAN%/lean}/leanchecker" "$module"
done
cd "$LANE"
"$LANE/scripts/run.sh" independent-python python3 -I "$LANE/scripts/sanity.py"
"$LANE/scripts/run.sh" independent-lean "$LEAN" -j1 -M3500 -DwarningAsError=true -o "$LANE/build/Sanity.olean" Sanity.lean
"$LANE/scripts/run.sh" check-Sanity "${LEAN%/lean}/leanchecker" Sanity
"$LANE/scripts/run.sh" verify-packet-audit python3 -I "$LANE/scripts/verify.py"
cd "$LANE/extracted"
for module in NegativeValue NegativeAdjacency NegativeConnected; do
 if "$LANE/scripts/run.sh" "negative-$module" "$LEAN" -j1 -M3500 -DwarningAsError=true "$module.lean"; then
   echo "Unexpected success: $module"; exit 1
 fi
done

#!/bin/bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
DIR=${1:-replay-fresh}
START=${2:-Hurlbert}
cd "$ROOT/$DIR"
source "$ROOT/scripts/env.sh"
LOG="$ROOT/logs/$DIR"
mkdir -p "$LOG"
"$ROOT/scripts/capped.sh" python3 -I -B "$ROOT/scripts/scan.py" "$DIR" > "$LOG/source-scan.log" 2>&1
ACTIVE=0
while read -r MODULE; do
 [ "$MODULE" != "$START" ] || ACTIVE=1
 [ "$ACTIVE" = 1 ] || continue
 echo "Building $MODULE"
 if "$ROOT/scripts/capped.sh" lean -j1 -M3500 -DwarningAsError=true -o "$MODULE.olean" "$MODULE.lean" > "$LOG/$MODULE.build.log" 2>&1; then
   echo "$MODULE build PASS" >> "$LOG/status.txt"
 else echo "$MODULE build FAIL" >> "$LOG/status.txt"; exit 1; fi
 echo "Checking $MODULE"
 if "$ROOT/scripts/capped.sh" leanchecker "$MODULE" > "$LOG/$MODULE.leanchecker.log" 2>&1; then
   echo "$MODULE leanchecker PASS" >> "$LOG/status.txt"
 else echo "$MODULE leanchecker FAIL" >> "$LOG/status.txt"; exit 1; fi
done < module-order.txt
[ "$ACTIVE" = 1 ]

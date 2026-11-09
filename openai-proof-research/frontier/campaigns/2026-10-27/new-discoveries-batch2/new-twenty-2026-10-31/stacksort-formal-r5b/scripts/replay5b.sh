#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
cd "$LANE/fresh-extraction/src"
for m in $(cat "$LANE/scripts/order.txt"); do
 if [ ! -f "$m.olean" ]; then
  STACKSORT_AUDIT_OUT="$LANE/logs/$m-audit.jsonl" "$LANE/scripts/run.sh" lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$LANE/logs/fresh-build-$m.log"
 fi
done
for m in $(cat "$LANE/scripts/order.txt"); do
 "$LANE/scripts/run.sh" leanchecker "$m" > "$LANE/logs/fresh-checker-$m.log"
done

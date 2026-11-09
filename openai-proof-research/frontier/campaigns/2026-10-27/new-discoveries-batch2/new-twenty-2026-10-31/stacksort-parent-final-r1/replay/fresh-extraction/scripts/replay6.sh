#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
if [ ! -d "$LANE/fresh-extraction/src" ]; then
 mkdir -p "$LANE/fresh-extraction"
 unzip -q "$LANE/stacksort-source6.zip" -d "$LANE/fresh-extraction"
fi
cd "$LANE/fresh-extraction/src"
for m in $(cat "$LANE/scripts/order.txt"); do
 if [ ! -f "$m.olean" ]; then
  STACKSORT_AUDIT_OUT="$LANE/logs/fresh-$m-audit.jsonl" "$LANE/scripts/run.sh" lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$LANE/logs/fresh-build-$m.log"
 fi
done
for m in $(cat "$LANE/scripts/order.txt"); do
 if [ ! -f "$LANE/logs/fresh-checker-$m.ok" ]; then
  "$LANE/scripts/run.sh" leanchecker "$m" > "$LANE/logs/fresh-checker-$m.log"
  touch "$LANE/logs/fresh-checker-$m.ok"
 fi
done
"$LANE/scripts/run.sh" python3 -I "$LANE/scripts/check_audit6.py" "$LANE/logs/fresh-StackSortAudit6-audit.jsonl" > "$LANE/logs/fresh-audit-summary.log"

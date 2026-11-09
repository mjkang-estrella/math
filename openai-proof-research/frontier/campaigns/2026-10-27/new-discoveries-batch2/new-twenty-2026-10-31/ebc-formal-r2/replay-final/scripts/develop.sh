#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
while read -r m; do
 cap lean -M3500 -DwarningAsError=true -o "$LANE/build/$m.olean" "$LANE/src/$m.lean" > "$LANE/logs/$m.dev.log" 2>&1 || { cat "$LANE/logs/$m.dev.log"; exit 1; }
 echo "$m compile PASS"
done < "$LANE/module-order.txt"

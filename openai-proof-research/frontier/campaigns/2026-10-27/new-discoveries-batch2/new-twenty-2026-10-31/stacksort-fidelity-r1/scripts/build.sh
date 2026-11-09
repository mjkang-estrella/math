#!/bin/bash
set -eu
L=$(cd "$(dirname "$0")/.." && pwd)
cd "$L/build/src"
while read -r m; do
 case "$m" in *Audit* ) continue;; esac
 [ ! -f "$m.olean" ] || continue
 echo "BUILD $m"
 "$L/scripts/run.sh" lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/build-$m.log"
done < "$L/build/scripts/order.txt"
"$L/scripts/run.sh" leanchecker StackSortFinal6 > "$L/logs/checker-StackSortFinal6.log"

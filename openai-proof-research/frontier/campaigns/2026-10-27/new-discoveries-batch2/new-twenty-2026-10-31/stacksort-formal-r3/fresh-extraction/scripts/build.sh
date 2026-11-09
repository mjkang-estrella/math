#!/bin/bash
set -eu
cd "$(dirname "$0")/../src"
for m in $(cat ../scripts/order.txt); do
 if [ ! -f "$m.olean" ] || [ "$m.lean" -nt "$m.olean" ]; then
 STACKSORT_AUDIT_OUT="$PWD/../logs/$m-audit.jsonl" ../scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "../logs/build-$m.log"
 fi
done

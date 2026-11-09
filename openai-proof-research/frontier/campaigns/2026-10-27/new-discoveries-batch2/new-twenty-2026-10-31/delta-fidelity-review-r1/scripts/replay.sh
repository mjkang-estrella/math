#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
cd "$lane/fresh/lean"
# Derive order from imports ourselves, independent of packet module lists/drivers.
for f in *.lean; do m=${f%.lean}; echo "$m $m"; awk '/^import /{for(i=2;i<=NF;i++)print $i}' "$f" | while read -r dep; do if [[ -f $dep.lean ]]; then echo "$dep $m"; fi; done; done | tsort > "$lane/import-order.txt"
: > "$lane/logs/replay.tsv"
while read -r m; do
 echo "BUILD $m"
 if "$lane/scripts/cap.sh" "build-$m" lean -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$lane/logs/build-$m.log" 2>&1; then
 echo -e "build\t$m\t$(cat "$lane/logs/build-$m.time")" >> "$lane/logs/replay.tsv"
 else echo "BUILD_FAIL $m"; exit 1; fi
 echo "CHECK $m"
 if "$lane/scripts/cap.sh" "check-$m" leanchecker "$m" > "$lane/logs/check-$m.log" 2>&1; then
 echo -e "check\t$m\t$(cat "$lane/logs/check-$m.time")" >> "$lane/logs/replay.tsv"
 else echo "CHECK_FAIL $m"; exit 1; fi
done < "$lane/import-order.txt"
echo REPLAY_COMPLETE

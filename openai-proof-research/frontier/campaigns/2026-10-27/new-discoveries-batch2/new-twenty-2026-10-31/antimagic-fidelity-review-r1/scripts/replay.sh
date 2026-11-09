#!/bin/bash
set -eu
L=$(cd "$(dirname "$0")/.." && pwd)
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
mkdir -p "$L/build"
export LEAN_PATH="$L/build"
for p in "$P"/*; do if [ -d "$p/.lake/build/lib/lean" ]; then export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; fi; done
cd "$L/fresh"
while read -r m; do
 echo "BUILD $m $(date -u +%FT%TZ)"
 "$L/scripts/capped.sh" "build-$m" lean -j1 -M3500 -DwarningAsError=true -o "$L/build/$m.olean" "$m.lean"
 "$L/scripts/capped.sh" "check-$m" leanchecker "$m"
 echo "PASS $m"
done < "$L/evidence/order.txt"
echo ALL_PASS

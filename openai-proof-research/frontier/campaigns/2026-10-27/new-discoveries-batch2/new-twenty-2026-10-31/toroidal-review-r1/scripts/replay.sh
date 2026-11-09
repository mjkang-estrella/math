#!/bin/bash
set -eu
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/toroidal-review-r1
M=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export PATH="$L/bin:/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH"
export LEAN_PATH="$L/build"
for p in "$M"/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
cd "$L/build"
for mod in Definitions Witness Audit; do
 cp "$L/packet/$mod.lean" "$mod.lean"
 "$L/scripts/capped.sh" lean -M3500 -DwarningAsError=true -o "$mod.olean" "$mod.lean" > "$L/logs/$mod.strict.log" 2>&1
 "$L/scripts/capped.sh" leanchecker "$mod" > "$L/logs/$mod.checker.log" 2>&1
 echo "$mod PASS"
done

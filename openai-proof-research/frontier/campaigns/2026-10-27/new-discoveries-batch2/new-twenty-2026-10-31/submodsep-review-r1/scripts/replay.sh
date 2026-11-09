#!/bin/bash
set -eu
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-review-r1
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$L/build/fresh/lean"
for p in "$P"/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
cd "$L/build/fresh/lean"
for mod in Separator Certificate Audit AuditAll ReviewAudit; do
 "$L/scripts/capped.sh" lean -M3500 -j2 -DwarningAsError=true -o "$mod.olean" "$mod.lean" > "$L/logs/lean-$mod.log" 2>&1
 echo "$mod strict rebuild PASS"
done
"$L/scripts/capped.sh" leanchecker -M3500 -j2 Certificate > "$L/logs/leanchecker.log" 2>&1
echo 'Explicit Certificate leanchecker PASS'

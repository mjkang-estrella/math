#!/bin/bash
set -eu
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r153
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$L/lean"
for p in "$P"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
cd "$L/lean"
exec "$L/scripts/cap.sh" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M3500 -DwarningAsError=true "$@"

#!/bin/bash
set -eu
LANE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r123"
CACHE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages"
export LEAN_PATH=$(find "$CACHE" -type d -path '*/.lake/build/lib/lean' | paste -sd:)
cd "$LANE/lean"
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j2 -M3500 -DmaxRecDepth=10000 -DmaxHeartbeats=4000000 -DwarningAsError=true -o Shrinking.olean Shrinking.lean

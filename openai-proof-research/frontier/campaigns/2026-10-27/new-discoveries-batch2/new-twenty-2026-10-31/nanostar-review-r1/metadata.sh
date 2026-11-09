#!/bin/bash
set -eu
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-review-r1
export LEAN_PATH="$PWD/build/lean"
for p in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
./cap.sh lean -M3500 -j1 -DwarningAsError=true build/lean/ReviewMetadata.lean >logs/review-metadata.log 2>&1

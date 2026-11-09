#!/bin/bash
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/delta-formal-r3
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
export LEAN_PATH="$LANE/build"
for p in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*; do
  export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"
done
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2

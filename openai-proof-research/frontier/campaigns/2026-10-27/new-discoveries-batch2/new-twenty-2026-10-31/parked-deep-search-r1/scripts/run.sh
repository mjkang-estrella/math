#!/bin/bash
set -eu
D=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/parked-deep-search-r1
export TMPDIR="$D/tmp" TMP="$D/tmp" TEMP="$D/tmp" XDG_CACHE_HOME="$D/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
exec perl "$D/scripts/cap.pl" "$@"

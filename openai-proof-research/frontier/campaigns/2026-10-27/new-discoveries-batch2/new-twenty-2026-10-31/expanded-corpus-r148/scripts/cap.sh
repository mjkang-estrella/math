#!/bin/bash
set -eu
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r148
export TMPDIR="$LANE/tmp" TMP="$LANE/tmp" TEMP="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONPYCACHEPREFIX="$LANE/cache" MALLOC_ARENA_MAX=2
ulimit -t 120
CPUS=$(awk '/Cpus_allowed_list/ {print $2}' /proc/self/status)
FIRST=${CPUS%%[-,]*}
SECOND=$((FIRST+1))
exec perl "$LANE/scripts/watch.pl" taskset -c "$FIRST,$SECOND" "$@"

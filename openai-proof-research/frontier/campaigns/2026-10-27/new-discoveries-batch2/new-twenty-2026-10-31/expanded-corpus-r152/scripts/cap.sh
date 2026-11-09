#!/bin/bash
set -u
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r152
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
setsid timeout -k 2 140 taskset -c 0,1 prlimit --cpu=120:120 --as=68719476736:68719476736 -- "$@" &
pid=$!
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo sid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
 if [ "$rss" -gt 6291456 ]; then kill -KILL -- -"$pid" 2>/dev/null; fi
 sleep .1
done
wait "$pid"

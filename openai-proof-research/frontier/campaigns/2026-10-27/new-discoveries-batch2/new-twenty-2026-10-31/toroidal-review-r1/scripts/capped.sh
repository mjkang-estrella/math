#!/bin/bash
set -eu
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/toroidal-review-r1
export TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/cache" PYTHONPYCACHEPREFIX="$L/cache" MALLOC_ARENA_MAX=2
# A separate process group permits killing the entire call, including descendants.
setsid timeout --signal=KILL 140 taskset -c 0,1 bash -c 'ulimit -t 120; exec "$@"' bash "$@" &
p=$!
(
 while kill -0 "$p" 2>/dev/null; do
   rss=$(ps -eo pgid=,rss= | awk -v p="$p" '$1==p {s+=$2} END {print s+0}')
   if [ "$rss" -gt 6291456 ]; then echo "RSS LIMIT $rss KiB" >&2; kill -KILL -- "-$p" 2>/dev/null || true; exit; fi
   sleep 0.2
 done
) &
w=$!
set +e
wait "$p"; rc=$?
kill "$w" 2>/dev/null; wait "$w" 2>/dev/null
exit "$rc"

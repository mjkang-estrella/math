#!/bin/bash
set -u
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/delta-formal-r2
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
ulimit -t 120
ulimit -c 0
setsid timeout --signal=KILL 140 taskset -c 0,1 "$@" &
pid=$!
(
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -ge 6291456 ]; then echo "RSS watchdog killed group $pid at $rss KiB" >&2; kill -KILL -- -"$pid" 2>/dev/null; exit; fi
 sleep 0.1
done
) &
watch=$!
wait "$pid"; status=$?
kill "$watch" 2>/dev/null || true
wait "$watch" 2>/dev/null || true
echo "resource_exit=$status" >&2
exit "$status"

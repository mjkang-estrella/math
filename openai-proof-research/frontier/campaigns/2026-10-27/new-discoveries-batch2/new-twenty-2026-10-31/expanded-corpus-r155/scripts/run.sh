#!/bin/bash
set -u
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r155
export TMPDIR="$L/tmp" XDG_CACHE_HOME="$L/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
ulimit -t 120
setsid timeout --signal=KILL 140 taskset -c 0,1 "$@" &
p=$!
(while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo sid=,rss= | awk -v p="$p" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo 'RSS LIMIT' >&2; kill -KILL -- -"$p"; break; fi
 sleep 0.2
done) &
w=$!
wait "$p"; rc=$?
kill "$w" 2>/dev/null || true
wait "$w" 2>/dev/null || true
exit "$rc"

#!/bin/bash
set -u
exec 9>/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-review-r1/tmp/heavy.lock
flock 9
cd /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/nanostar-review-r1
export TMPDIR="$PWD/tmp" XDG_CACHE_HOME="$PWD/tmp/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
ulimit -t 120
setsid timeout --signal=KILL 140s taskset -c 0,1 "$@" &
p=$!
(while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo sid=,rss= | awk -v p="$p" '$1==p {s+=$2} END {print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo "RSS LIMIT $rss" >&2; kill -KILL -- -"$p" 2>/dev/null; break; fi
 sleep 0.3
done) &
w=$!
wait "$p"; status=$?
kill "$w" 2>/dev/null; wait "$w" 2>/dev/null
exit "$status"

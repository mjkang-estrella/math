#!/bin/bash
set -u
D=$(cd -- "$(dirname -- "$0")/.." && pwd)
export TMPDIR="$D/tmp" XDG_CACHE_HOME="$D/cache" PYTHONPYCACHEPREFIX="$D/cache" MALLOC_ARENA_MAX=2
setsid timeout -k 3 140 bash -c 'ulimit -t 120; exec taskset -c 0,1 "$@"' cap "$@" &
p=$!
(while kill -0 "$p" 2>/dev/null; do rss=$(ps -eo pgid=,rss= | awk -v p="$p" '$1==p{s+=$2}END{print s+0}'); if [ "$rss" -gt 6291456 ]; then echo 'RSS LIMIT' >&2; kill -KILL -- -"$p" 2>/dev/null; break; fi; sleep 0.2; done) &
w=$!
wait "$p"; rc=$?
kill "$w" 2>/dev/null; wait "$w" 2>/dev/null
exit "$rc"

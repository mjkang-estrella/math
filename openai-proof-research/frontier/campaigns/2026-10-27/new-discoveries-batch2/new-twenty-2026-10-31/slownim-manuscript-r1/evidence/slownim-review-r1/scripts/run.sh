#!/bin/bash
set -u
lane=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$lane/tmp" XDG_CACHE_HOME="$lane/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
ulimit -t 120
# timeout starts a separate process group; sum RSS of all members, not just parent.
timeout -k 2s 140s taskset -c 0,1 "$@" &
pid=$!
( while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo 'RSS cap exceeded' >&2; kill -KILL -- "-$pid" 2>/dev/null; break; fi
 sleep 0.2
 done ) &
watch=$!
wait "$pid"; status=$?
kill "$watch" 2>/dev/null || true
wait "$watch" 2>/dev/null || true
exit "$status"

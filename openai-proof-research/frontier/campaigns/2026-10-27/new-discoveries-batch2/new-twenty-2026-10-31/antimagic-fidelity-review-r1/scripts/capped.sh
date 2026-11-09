#!/bin/bash
set -u
L=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/cache" PYTHONPYCACHEPREFIX="$L/cache/pycache" MALLOC_ARENA_MAX=2
name=$1; shift
setsid bash -c 'ulimit -t 120; exec /usr/bin/time -f "elapsed=%e max_rss_kib=%M exit=%x" timeout --foreground -k 2 140 taskset -c 0,1 "$@"' bash "$@" > "$L/logs/$name.log" 2>&1 &
pid=$!
(while kill -0 "$pid" 2>/dev/null; do rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}'); if [ "$rss" -ge 6291456 ]; then echo "RSS_WATCHDOG $rss" >> "$L/logs/$name.log"; kill -KILL -- -"$pid" 2>/dev/null; break; fi; sleep 0.2; done) &
watch=$!
trap 'kill -KILL -- -"$pid" 2>/dev/null; kill "$watch" 2>/dev/null' TERM INT
wait "$pid"; rc=$?
kill "$watch" 2>/dev/null; wait "$watch" 2>/dev/null
exit "$rc"

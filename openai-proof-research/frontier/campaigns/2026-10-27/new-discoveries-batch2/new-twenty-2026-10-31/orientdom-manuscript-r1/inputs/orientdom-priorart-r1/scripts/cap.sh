#!/bin/bash
set -u
ROOT=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/orientdom-priorart-r1
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/tmp" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
CPUS=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status | awk -F '[-,]' '{print $1","$1+1}')
NAME=$1; shift
setsid timeout -s KILL 140 taskset -c "$CPUS" bash -c 'ulimit -t 120; exec "$@"' bash "$@" >"$ROOT/logs/$NAME.log" 2>&1 &
PID=$!
(while kill -0 "$PID" 2>/dev/null; do
 RSS=$(ps -eo pgid=,rss= | awk -v p="$PID" '$1==p {s+=$2} END{print s+0}')
 if [ "$RSS" -gt 6291456 ]; then echo "RSS limit $RSS" >>"$ROOT/logs/$NAME.watch"; kill -KILL -- -"$PID" 2>/dev/null; break; fi
 echo "$RSS" >>"$ROOT/logs/$NAME.watch"
 sleep 0.2
done) & WATCH=$!
wait "$PID"; RC=$?
kill "$WATCH" 2>/dev/null; wait "$WATCH" 2>/dev/null
printf 'exit=%s\n' "$RC" >"$ROOT/logs/$NAME.receipt"
exit "$RC"

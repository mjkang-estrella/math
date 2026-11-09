#!/bin/bash
set -u
ROOT=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/hurlbert-review-r1
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
CPUS=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status)
FIRST=${CPUS%%[-,]*}; SECOND=$((FIRST+1))
(ulimit -t 120; exec setsid timeout -k 2 140 taskset -c "$FIRST,$SECOND" "$@") & PID=$!
(while kill -0 "$PID" 2>/dev/null; do
 RSS=$(ps -eo rss=,pgid= | awk -v g="$(ps -o pgid= -p "$PID" | tr -d ' ')" '$2==g {s+=$1} END{print s+0}')
 if [ "$RSS" -gt 6291456 ]; then kill -KILL -- "-$PID" 2>/dev/null; exit; fi
 sleep 0.25
done) & WATCH=$!
wait "$PID"; RC=$?; kill "$WATCH" 2>/dev/null; wait "$WATCH" 2>/dev/null; exit "$RC"

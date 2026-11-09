#!/bin/bash
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
mkdir -p "$TMPDIR" "$XDG_CACHE_HOME"
CPUS=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status)
FIRST=${CPUS%%[-,]*}; SECOND=$((FIRST+1))
(ulimit -t 120; exec setsid timeout -k 2 140 taskset -c "$FIRST,$SECOND" "$@") & PID=$!
(while kill -0 "$PID" 2>/dev/null; do
 RSS=$(ps -eo rss=,pgid= | awk -v g="$PID" '$2==g {s+=$1} END{print s+0}')
 if [ "$RSS" -gt 6291456 ]; then echo "RSS watchdog exceeded 6 GiB" >&2; kill -KILL -- "-$PID" 2>/dev/null || true; exit; fi
 sleep 0.25
done) & WATCH=$!
trap 'kill -KILL -- "-$PID" 2>/dev/null || true; kill "$WATCH" 2>/dev/null || true' INT TERM EXIT
set +e
wait "$PID"; RC=$?
kill "$WATCH" 2>/dev/null; wait "$WATCH" 2>/dev/null
trap - INT TERM EXIT
exit "$RC"

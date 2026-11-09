#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
ulimit -t 120
# Address-space limit is an additional safeguard; RSS is independently watched.
ulimit -v 6291456
timeout -k 2s 140s taskset -c 0,1 "$@" &
pid=$!
trap 'kill "$pid" 2>/dev/null || true' EXIT INT TERM
while kill -0 "$pid" 2>/dev/null; do
  for child in "$pid" $(pgrep -P "$pid" || true); do
    if [ -r "/proc/$child/status" ]; then
      rss=$(awk '/^VmRSS:/ {print $2}' "/proc/$child/status" 2>/dev/null || true)
      if [ "${rss:-0}" -gt 6291456 ]; then kill -KILL "$child" "$pid" 2>/dev/null || true; fi
    fi
  done
  sleep 0.2
done
wait "$pid"
trap - EXIT

#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" MALLOC_ARENA_MAX=2 LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD:$PKG/mathlib/.lake/build/lib/lean"
for p in "$PKG"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
LOG="$LANE/logs/$(date -u +%Y%m%dT%H%M%S%N).log"
printf '%q ' "$@" > "$LOG"
printf '\n' >> "$LOG"
set +e
(ulimit -c 0; ulimit -t 120; exec /usr/bin/time -v timeout --kill-after=2 140 taskset -c 0,1 "$@") >> "$LOG" 2>&1 &
PID=$!
# Inspect all descendants, including Python itself, every 50 ms.
(
 while kill -0 "$PID" 2>/dev/null; do
  todo="$PID"; rss=0; ids=""
  while [ -n "$todo" ]; do
   next=""
   for p in $todo; do
    ids="$ids $p"
    if [ -r "/proc/$p/status" ]; then
     r=$(awk '/^VmRSS:/{print $2}' "/proc/$p/status" 2>/dev/null)
     rss=$((rss + ${r:-0}))
     next="$next $(cat "/proc/$p/task/$p/children" 2>/dev/null)"
    fi
   done
   todo="$next"
  done
  if [ "$rss" -gt 6291456 ]; then
   echo "RSS CAP EXCEEDED $rss KiB" >> "$LOG"
   kill -KILL $ids 2>/dev/null
   break
  fi
  sleep .05
 done
) &
MON=$!
wait "$PID"; RC=$?
kill "$MON" 2>/dev/null
wait "$MON" 2>/dev/null
printf '\nexit %s\n' "$RC" >> "$LOG"
cat "$LOG"
exit "$RC"

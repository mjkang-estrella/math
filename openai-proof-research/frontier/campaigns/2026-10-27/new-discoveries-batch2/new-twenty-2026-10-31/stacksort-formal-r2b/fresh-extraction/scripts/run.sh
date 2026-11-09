#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2 LEAN_NUM_THREADS=1
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD:$LANE/build:$PKG/mathlib/.lake/build/lib/lean"
for p in "$PKG"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
CPUS=$(awk '/Cpus_allowed_list/ {split($2,a,"[-,]"); print a[1] "," a[1]+1}' /proc/self/status)
LOG="$LANE/logs/$(date -u +%Y%m%dT%H%M%S%N).log"
printf '%q ' "$@" > "$LOG"; printf '\n' >> "$LOG"
(ulimit -c 0; ulimit -t 120; exec setsid /usr/bin/time -v timeout --kill-after=2 140 taskset -c "$CPUS" "$@") >> "$LOG" 2>&1 &
PID=$!
watch() {
 while kill -0 "$PID" 2>/dev/null; do
  RSS=$(ps -eo pid=,ppid=,rss= | awk -v root="$PID" '{p[$1]=$2;r[$1]=$3} END {for(i in p){j=i; for(k=0;k<20 && j!=root && j in p;k++)j=p[j];if(j==root)t+=r[i]} print t+0}')
  if [ "$RSS" -gt 6291456 ]; then
   echo "RSS CAP EXCEEDED $RSS" >> "$LOG"
   kill -KILL -- -"$PID" 2>/dev/null || true; return
  fi
  sleep .05
 done
}
watch & WATCH=$!
trap 'kill "$WATCH" 2>/dev/null || true; kill -KILL -- -"$PID" 2>/dev/null || true' EXIT
set +e
wait "$PID"; RC=$?
kill "$WATCH" 2>/dev/null; wait "$WATCH" 2>/dev/null
printf '\nexit %s\n' "$RC" >> "$LOG"
cat "$LOG"
exit "$RC"

#!/bin/bash
set -u
cd "$(dirname "$0")"
export TMPDIR="$PWD/tmp" XDG_CACHE_HOME="$PWD/cache" MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
export PATH="$PWD/bin:$PATH"
pkg=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD/build"
for d in "$pkg"/*; do
  if [ -d "$d/.lake/build/lib/lean" ]; then export LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; fi
done
(ulimit -t 120; exec timeout --signal=KILL 140 taskset -c 0,1 "$@") &
job=$!
(
while kill -0 "$job" 2>/dev/null; do
  rss=$(ps -eo pid,ppid,rss | awk -v root="$job" '{p[NR]=$1; pp[$1]=$2; r[$1]=$3} END {s=0; for(i=1;i<=NR;i++){x=p[i]; for(k=0;k<12;k++){if(x==root){s+=r[p[i]];break} x=pp[x];if(!x)break}} print s}')
  if [ "${rss:-0}" -gt 6291456 ]; then pkill -KILL -P "$job" 2>/dev/null; kill -KILL "$job" 2>/dev/null; exit; fi
  sleep 0.25
done
) &
monitor=$!
wait "$job"
status=$?
pkill -KILL -P "$monitor" 2>/dev/null || true
kill "$monitor" 2>/dev/null
wait "$monitor" 2>/dev/null
exit "$status"

#!/bin/bash
set -u
lane=$(cd "$(dirname "$0")" && pwd)
export TMPDIR="$lane/tmp" MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
label=$1; shift
mkdir -p "$lane/logs"
start=$SECONDS
setsid timeout -k 1 140 taskset -c 0,1 prlimit --cpu=120:120 -- /usr/bin/time -v "$@" >"$lane/logs/$label.log" 2>&1 &
leader=$!
peak=0
while kill -0 "$leader" 2>/dev/null; do
 total=0
 for p in $(ps -eo pid,pgid | awk -v g="$leader" '$2==g {print $1}'); do
  rss=$(awk '/VmRSS:/ {print $2}' /proc/$p/status 2>/dev/null); total=$((total+${rss:-0}))
 done
 ((total>peak)) && peak=$total
 if ((total>6291456)); then kill -KILL -- -"$leader" 2>/dev/null; fi
 sleep 0.1
done
wait "$leader"; rc=$?
printf '{"exit":%s,"seconds":%s,"peak_group_rss_kib":%s}\n' "$rc" "$((SECONDS-start))" "$peak" >"$lane/logs/$label.receipt.json"
cat "$lane/logs/$label.receipt.json"
exit "$rc"

#!/bin/bash
set -u
export MALLOC_ARENA_MAX=2 TMPDIR="$PWD/tmp" PYTHONDONTWRITEBYTECODE=1
label=$1; shift
start=$SECONDS
timeout -k 2 140 taskset -c 0,1 prlimit --cpu=120:120 -- "$@" >"logs/$label.log" 2>&1 &
leader=$!
peak=0
while kill -0 "$leader" 2>/dev/null; do
 total=0
 for p in $(ps -eo pid,pgid | awk -v g="$leader" '$2==g {print $1}'); do
  rss=$(awk '/VmRSS:/ {print $2}' /proc/$p/status 2>/dev/null); total=$((total+${rss:-0}))
 done
 ((total>peak)) && peak=$total
 if ((total>6291456)); then kill -KILL -- -"$leader" 2>/dev/null; fi
 sleep 0.15
done
wait "$leader"; rc=$?
printf '{"exit":%s,"seconds":%s,"peak_group_rss_kib":%s}\n' "$rc" "$((SECONDS-start))" "$peak" >"logs/$label.receipt.json"
cat "logs/$label.receipt.json"
exit "$rc"

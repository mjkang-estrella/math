#!/bin/bash
set -u
R=$(cd "$(dirname "$0")" && pwd)
export TMPDIR="$R/tmp" XDG_CACHE_HOME="$R/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
mkdir -p "$TMPDIR" "$XDG_CACHE_HOME" "$R/logs"
label=$1; shift
setsid timeout -k 1 140 taskset -c 0,1 prlimit --cpu=120:120 -- /usr/bin/time -v "$@" > "$R/logs/$label.log" 2>&1 &
pid=$!; peak=0; start=$SECONDS
while kill -0 "$pid" 2>/dev/null; do
 rss=0
 for p in $(ps -eo pid,pgid | awk -v g="$pid" '$2==g {print $1}'); do
  v=$(awk '/VmRSS:/ {print $2}' /proc/$p/status 2>/dev/null); rss=$((rss+${v:-0}))
 done
 ((rss>peak)) && peak=$rss
 if ((rss>6291456)); then kill -KILL -- -"$pid" 2>/dev/null; fi
 sleep 0.1
done
wait "$pid"; rc=$?
printf '{"exit":%d,"seconds":%d,"peak_rss_kib":%d}\n' "$rc" "$((SECONDS-start))" "$peak" | tee "$R/logs/$label.json"
exit "$rc"

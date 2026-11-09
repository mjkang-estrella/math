#!/bin/bash
set -u
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
tag=$1; shift
log="$LANE/logs/$(date +%s%N)-$tag"
setsid timeout -k 2 140 prlimit --cpu=120:120 -- taskset -c 0,1 "$@" >"$log.out" 2>"$log.err" &
pid=$!
peak=0
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -o rss= --sid "$pid" | awk '{s+=$1} END{print s+0}')
 ((rss>peak)) && peak=$rss
 if ((rss>6291456)); then kill -KILL -- "-$pid" 2>/dev/null; fi
 sleep 0.2
done
wait "$pid"; rc=$?
printf 'exit=%s peak_rss_kib=%s\n' "$rc" "$peak" >"$log.receipt"
cat "$log.out" "$log.err" "$log.receipt"
exit "$rc"

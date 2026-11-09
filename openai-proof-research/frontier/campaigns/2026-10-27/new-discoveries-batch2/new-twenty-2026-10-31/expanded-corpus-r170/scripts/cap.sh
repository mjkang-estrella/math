#!/bin/bash
set -u
L="$(cd "$(dirname "$0")/.." && pwd)"
export TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
ulimit -t 120
setsid timeout -k 2 140 taskset -c 0,1 "$@" &
p=$!
(
while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$p" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -gt 1572864 ]; then echo "RSS_LIMIT $rss" >&2; kill -KILL -- "-$p" 2>/dev/null; break; fi
 sleep 0.3
done
) &
w=$!
wait "$p"; r=$?
kill "$w" 2>/dev/null
wait "$w" 2>/dev/null
exit "$r"

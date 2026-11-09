#!/bin/bash
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
export TMPDIR="$LANE/tmp" TMP="$LANE/tmp" TEMP="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
setsid timeout -k 2 140 taskset -c 0,1 prlimit --cpu=120:120 --as=68719476736 -- "$@" &
p=$!
trap 'kill -KILL -- -"$p" 2>/dev/null || true; wait "$p" 2>/dev/null || true' EXIT INT TERM
while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo sid=,rss= | awk -v p="$p" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo "RSS watchdog killed $rss KiB" >&2; kill -KILL -- -"$p" 2>/dev/null || true; fi
 sleep 0.2
done
wait "$p"; r=$?
trap - EXIT INT TERM
exit "$r"

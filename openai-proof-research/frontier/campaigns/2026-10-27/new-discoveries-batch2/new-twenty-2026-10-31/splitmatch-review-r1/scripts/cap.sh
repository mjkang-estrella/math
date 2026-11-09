#!/bin/bash
set -u
L=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$L/tmp" XDG_CACHE_HOME="$L/tmp" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
CPUS=$(awk '/Cpus_allowed_list/ {print $2}' /proc/self/status | awk -F '[-,]' '{print $1","$1+1}')
setsid timeout -k 3s 140s taskset -c "$CPUS" prlimit --cpu=120:120 -- "$@" &
p=$!
(while kill -0 "$p" 2>/dev/null; do
 rss=$(ps -eo sid=,rss= | awk -v p="$p" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo "RSS limit exceeded: $rss KiB" >&2; kill -KILL -- -"$p" 2>/dev/null; exit; fi
 sleep 0.2
done) &
w=$!
wait "$p"; r=$?
kill "$w" 2>/dev/null; wait "$w" 2>/dev/null
exit "$r"

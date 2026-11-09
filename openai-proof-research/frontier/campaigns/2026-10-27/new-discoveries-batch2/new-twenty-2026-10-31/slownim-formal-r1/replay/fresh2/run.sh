#!/bin/bash
set -u
LANE=$(cd "$(dirname "$0")" && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp/cache" MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build"
for p in "$PKG"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
setsid timeout -k 2 140 taskset -c 0,1 bash -c 'ulimit -t 120; exec "$@"' _ "$@" &
pid=$!
(while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
 if [ "$rss" -gt 6291456 ]; then kill -KILL -- -"$pid"; exit 1; fi
 sleep 0.2
done) &
watch=$!
wait "$pid"; result=$?
kill "$watch" 2>/dev/null || true
wait "$watch" 2>/dev/null || true
exit "$result"

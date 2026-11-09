#!/usr/bin/env bash
set -u
LANE=$(cd "$(dirname "$0")" && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp/cache" MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
PACK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build:$LANE/src"
for p in "$PACK"/*; do LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export LEAN_PATH
setsid timeout -k 2s 140s taskset -c 0,1 bash -c 'ulimit -t 120; exec /usr/bin/time -v "$@"' bash "$@" &
pid=$!
(
 while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
  if [ "$rss" -ge 6291456 ]; then echo "RSS LIMIT $rss KiB" >&2; kill -KILL -- -"$pid" 2>/dev/null; break; fi
  sleep 0.1
 done
) &
watch=$!
trap 'kill -- -"$pid" 2>/dev/null || :; kill "$watch" 2>/dev/null || :; wait "$watch" 2>/dev/null || :' EXIT
wait "$pid"
status=$?
exit "$status"

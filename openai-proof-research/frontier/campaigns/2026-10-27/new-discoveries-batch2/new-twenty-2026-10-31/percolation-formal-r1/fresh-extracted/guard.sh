#!/usr/bin/env bash
set -eu
ROOT=$(cd -- "$(dirname -- "$0")" && pwd)
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/tmp/cache" PYTHONPYCACHEPREFIX="$ROOT/tmp/pycache" MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
ulimit -t 120
# The wrapped tools do not fork workers; kill the entire process group on excess RSS.
taskset -c 0,1 timeout --signal=KILL 140s "$@" &
job=$!
trap 'kill "$job" 2>/dev/null || true' EXIT
while kill -0 "$job" 2>/dev/null; do
  rss=$(ps -o rss= -p "$job" --ppid "$job" | awk '{s+=$1} END {print s+0}')
  if [ "$rss" -gt 6291456 ]; then
    pkill -KILL -P "$job" || true
    kill -KILL "$job" || true
    echo 'RSS watchdog exceeded 6 GiB' >&2
    break
  fi
  sleep 0.2
done
wait "$job"

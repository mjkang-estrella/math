#!/usr/bin/env bash
set -eu
ROOT=$(cd -- "$(dirname -- "$0")" && pwd)
mkdir -p "$ROOT/tmp/cache" "$ROOT/tmp/pycache"
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/tmp/cache" PYTHONPYCACHEPREFIX="$ROOT/tmp/pycache" MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
ulimit -t 120
taskset -c 0,1 timeout --signal=KILL 140s "$@" &
job=$!
cleanup() { pkill -KILL -P "$job" 2>/dev/null || true; kill -KILL "$job" 2>/dev/null || true; }
trap cleanup EXIT INT TERM
while kill -0 "$job" 2>/dev/null; do
  rss=$(ps -o rss= -p "$job" --ppid "$job" | awk '{s+=$1} END {print s+0}')
  if [ "$rss" -gt 6291456 ]; then cleanup; echo 'RSS watchdog exceeded 6 GiB' >&2; break; fi
  sleep 0.2
done
wait "$job"

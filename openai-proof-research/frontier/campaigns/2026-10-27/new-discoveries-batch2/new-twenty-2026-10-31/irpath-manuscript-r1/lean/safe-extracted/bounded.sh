#!/bin/bash
set -u
cd "$(dirname "$0")"
export TMPDIR="$PWD/tmp" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
setsid timeout -s KILL 140 taskset -c 0,1 bash -c 'ulimit -c 0; ulimit -t 120; exec "$@"' bash "$@" &
pid=$!
( while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}')
 if [ "$rss" -gt 6291456 ]; then echo 'RSS watchdog exceeded' >&2; kill -KILL -- -"$pid"; exit; fi
 sleep 0.3
 done ) &
watch=$!
wait "$pid"
rc=$?
kill "$watch" 2>/dev/null || true
wait "$watch" 2>/dev/null || true
exit "$rc"

#!/usr/bin/env bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONPYCACHEPREFIX="$LANE/cache/py" MALLOC_ARENA_MAX=2
mkdir -p "$TMPDIR" "$XDG_CACHE_HOME" "$LANE/logs"
name=$1; shift
log="$LANE/logs/${name}-$(date +%s%N)"
(ulimit -t 120; exec setsid timeout --signal=KILL 140 taskset -c 0,1 "$@") >"$log.out" 2>"$log.err" &
pid=$!
(
 while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
  if [ "$rss" -gt 6291456 ]; then echo "RSS watchdog killed group $pid at $rss KiB" >>"$log.err"; kill -KILL -- "-$pid" 2>/dev/null || true; break; fi
  sleep 0.1
 done
) &
watch=$!
set +e
wait "$pid"; rc=$?
kill "$watch" 2>/dev/null; wait "$watch" 2>/dev/null
set -e
printf '%s\n' "exit=$rc" >>"$log.err"
cat "$log.out" "$log.err"
exit "$rc"

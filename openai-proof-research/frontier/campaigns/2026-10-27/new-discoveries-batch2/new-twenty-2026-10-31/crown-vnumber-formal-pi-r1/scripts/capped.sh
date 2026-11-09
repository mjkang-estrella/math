#!/bin/bash
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$ROOT/tmp" XDG_CACHE_HOME="$ROOT/cache" MALLOC_ARENA_MAX=2
stamp=$(date +%s%N)
log="$ROOT/logs/$stamp.log"
{
  echo "CMD=$(printf %q "$@")"
  echo "ENV LEAN_PATH=$LEAN_PATH"
} >>"$log"
(
 ulimit -t 120
 exec setsid timeout --signal=KILL 140 taskset -c 0,1 "$@"
) >>"$log" 2>&1 &
pid=$!
(
 peak=0
 while kill -0 "$pid" 2>/dev/null; do
   rss=$(ps -eo sid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}')
   if ((rss>peak)); then peak=$rss; fi
   if ((rss>6291456)); then echo "RSS_LIMIT $rss" >>"$log"; kill -KILL -- -"$pid" 2>/dev/null || true; break; fi
   sleep 0.1
 done
 echo "PEAK_RSS_KIB=$peak" >>"$log"
) &
watch=$!
set +e
wait "$pid"; status=$?
wait "$watch"
set -e
echo "EXIT=$status" >>"$log"
tail -5 "$log"
echo "LOG=$log EXIT=$status"
exit "$status"

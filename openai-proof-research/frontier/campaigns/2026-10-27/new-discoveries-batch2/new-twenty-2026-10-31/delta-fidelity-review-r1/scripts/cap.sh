#!/bin/bash
set -u
lane=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$lane/tmp" XDG_CACHE_HOME="$lane/cache" PYTHONPYCACHEPREFIX="$lane/cache/py" MALLOC_ARENA_MAX=2
label=$1; shift
exec 9>"$lane/process.lock"
flock 9
setsid bash -c 'ulimit -t 120; exec timeout -k 2 140 taskset -c 0,1 /usr/bin/time -f "%e %U %S %M %x" -o "$1" "${@:2}"' bash "$lane/logs/$label.time" "$@" &
pid=$!
(while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}')
 if ((rss>6291456)); then echo "RSS_CAP $rss" > "$lane/logs/$label.cap"; kill -KILL -- -"$pid" 2>/dev/null; exit; fi
 sleep 0.2
done) &
watch=$!
wait "$pid"; rc=$?
kill "$watch" 2>/dev/null; wait "$watch" 2>/dev/null
exit "$rc"

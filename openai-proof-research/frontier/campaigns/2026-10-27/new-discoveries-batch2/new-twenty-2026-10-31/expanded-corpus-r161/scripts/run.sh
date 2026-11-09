#!/bin/bash
set -u
D=$(cd -- "$(dirname -- "$0")/.." && pwd)
export TMPDIR="$D/tmp" XDG_CACHE_HOME="$D/cache" PYTHONPYCACHEPREFIX="$D/cache/pycache" MALLOC_ARENA_MAX=2 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=2
name=$1; shift
cpus=$(awk '/Cpus_allowed_list/ {print $2}' /proc/self/status)
first=$(echo "$cpus" | sed 's/[-,].*//'); second=$((first+1))
start=$SECONDS
setsid timeout -k 2 140 taskset -c "$first,$second" bash -c 'ulimit -t 120; exec "$@"' _ "$@" > "$D/logs/$name.log" 2>&1 &
pid=$!
peak=0
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -e -o pgid=,rss= | awk -v p="$pid" '$1==p {s+=$2} END {print s+0}')
 ((rss>peak)) && peak=$rss
 if ((rss>6291456)); then kill -KILL -- -"$pid" 2>/dev/null; break; fi
 sleep 0.1
done
wait "$pid"; code=$?
printf 'exit=%s wall=%s peak_group_rss_KiB=%s CPU=120 wall_cap=140 RSS_cap_KiB=6291456 CPUs=%s,%s\n' "$code" "$((SECONDS-start))" "$peak" "$first" "$second" > "$D/logs/$name.receipt.txt"
cat "$D/logs/$name.receipt.txt"
exit "$code"

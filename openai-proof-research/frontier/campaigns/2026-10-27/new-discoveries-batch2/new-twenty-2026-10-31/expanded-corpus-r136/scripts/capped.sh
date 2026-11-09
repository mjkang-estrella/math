#!/bin/bash
set -u
D=$(cd "$(dirname "$0")/.." && pwd)
name=$1
shift
cpus=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status)
first=${cpus%%[-,]*}
second=$((first+1))
export MALLOC_ARENA_MAX=2 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=2 TMPDIR="$D"
start=$SECONDS
setsid taskset -c "$first,$second" timeout -k 2 140 prlimit --cpu=120:120 -- "$@" > "$D/logs/$name.log" 2>&1 &
pid=$!
peak=0
reason=none
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2}END{print s+0}')
 ((rss>peak)) && peak=$rss
 if ((rss>6291456)); then reason=rss; kill -KILL -- -"$pid" 2>/dev/null; fi
 if ((SECONDS-start>142)); then reason=wall; kill -KILL -- -"$pid" 2>/dev/null; fi
 sleep 0.1
done
wait "$pid"
rc=$?
printf '{"exit":%s,"peak_group_rss_kib":%s,"seconds":%s,"cap_reason":"%s","limits":"2 CPUs, 120 CPU seconds, 140 wall seconds, sampled aggregate RSS 6 GiB"}\n' "$rc" "$peak" "$((SECONDS-start))" "$reason" > "$D/logs/$name.receipt.json"
cat "$D/logs/$name.receipt.json"
exit "$rc"

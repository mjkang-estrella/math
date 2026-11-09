#!/bin/bash
set -u
D=$(cd "$(dirname "$0")/.." && pwd)
name=$1; shift
export PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=2 TMPDIR="$D/outputs"
cpus=$(awk '/Cpus_allowed_list/ {print $2}' /proc/self/status)
first=${cpus%%[-,]*}; second=$((first+1))
(ulimit -t 120; exec timeout -k 1 140 taskset -c "$first,$second" "$@") > "$D/logs/$name.log" 2>&1 &
pid=$!
peak=0
while kill -0 "$pid" 2>/dev/null; do
 rss=$(ps -eo pid,ppid,rss | awk -v root="$pid" '{p[NR]=$1; q[NR]=$2; r[NR]=$3} END {s[root]=1; for(j=0;j<10;j++) for(i=1;i<=NR;i++) if(s[q[i]])s[p[i]]=1; for(i=1;i<=NR;i++)if(s[p[i]])sum+=r[i];print sum+0}')
 ((rss>peak)) && peak=$rss
 if ((rss>6291456)); then pkill -KILL -P "$pid" || true; kill -KILL "$pid" || true; fi
 sleep .1
done
wait "$pid"; rc=$?
printf '{"exit_code":%s,"sampled_tree_peak_kib":%s,"rss_cap_kib":6291456,"cpu_seconds":120,"wall_seconds":140,"cpus":2}\n' "$rc" "$peak" > "$D/logs/$name.receipt.json"
cat "$D/logs/$name.receipt.json"
exit "$rc"

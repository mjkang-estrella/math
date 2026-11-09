#!/bin/bash
set -u
export MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
cpus=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status | cut -d, -f1 | awk -F- '{if(NF==1)print $1;else print $1"-"$1+1}')
setsid timeout -k 2s 140s taskset -c "$cpus" bash -c 'ulimit -t 120; exec "$@"' cap "$@" &
pid=$!
(while kill -0 "$pid" 2>/dev/null; do rss=$(ps -eo sid=,rss= | awk -v p="$pid" '$1==p{s+=$2}END{print s+0}'); if [ "$rss" -gt 6291456 ]; then kill -KILL -- -"$pid"; break; fi; sleep 0.2; done) &
watch=$!
wait "$pid"; rc=$?
kill "$watch" 2>/dev/null || true
wait "$watch" 2>/dev/null || true
exit "$rc"

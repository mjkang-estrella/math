#!/bin/bash
set -u
export MALLOC_ARENA_MAX=2
ulimit -t 120
setsid timeout -k 2 140 taskset -c 0,1 "$@" &
pid=$!
trap 'kill -KILL -- -"$pid" 2>/dev/null || true' EXIT INT TERM
peak=0
while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2}END{print s+0}')
  ((rss>peak)) && peak=$rss
  if ((rss>6291456)); then kill -KILL -- -"$pid" 2>/dev/null; echo 'RSS LIMIT' >&2; fi
  sleep 0.1
done
wait "$pid"; rc=$?
echo "exit=$rc peak_sampled_rss_kib=$peak" >&2
trap - EXIT
exit "$rc"

#!/bin/bash
set -u
BASE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-retention-r1
export TMPDIR="$BASE/tmp" XDG_CACHE_HOME="$BASE/tmp/cache" PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
CPUS=$(awk '/Cpus_allowed_list/{print $2}' /proc/self/status | awk -F'[-,]' '{print $1}')
CPU2=$((CPUS+1))
setsid timeout --signal=TERM --kill-after=2 140 taskset -c "$CPUS,$CPU2" prlimit --cpu=120 -- "$@" &
pid=$!
peak=0; started=$SECONDS
while kill -0 "$pid" 2>/dev/null; do
  rss=$(ps -eo pgid=,rss= | awk -v p="$pid" '$1==p{s+=$2} END{print s+0}')
  if [ "$rss" -gt "$peak" ]; then peak=$rss; fi
  if [ "$rss" -gt 6291456 ]; then echo "RSS LIMIT $rss" >&2; kill -KILL -- -"$pid" 2>/dev/null; fi
  sleep 0.2
done
wait "$pid"; rc=$?
printf '{"exit_code":%s,"peak_group_rss_kib":%s,"wall_seconds":%s}\n' "$rc" "$peak" "$((SECONDS-started))" > "$BASE/logs/cap-$pid.json"
exit "$rc"

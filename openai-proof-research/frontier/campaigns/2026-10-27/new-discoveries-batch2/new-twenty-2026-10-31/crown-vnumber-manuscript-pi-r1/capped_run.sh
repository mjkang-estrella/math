#!/usr/bin/env bash
# Capped job runner for the manuscript lane. Logs to logs/jobs.jsonl.
# Heavy jobs: <=2 CPUs (taskset), CPU 120s, wall 140s, AS 12GiB, RSS guard 6GiB (sampled), MALLOC_ARENA_MAX=2.
set -u
LANE="$(cd "$(dirname "$0")" && pwd)"
LOG="$LANE/logs/jobs.jsonl"
mkdir -p "$LANE/logs"
job="$1"; shift
start=$(date +%s.%N)
ulimit -t 120 2>/dev/null || true
ulimit -v 12582912 2>/dev/null || true
export MALLOC_ARENA_MAX=2
# RSS guard sampler: kills the process group if sampled RSS > 6GiB
( while sleep 2; do
    rss=$(ps -o rss= -g $$ 2>/dev/null | awk '{s+=$1} END {print s+0}')
    if [ "${rss:-0}" -gt 6291456 ]; then
      kill -9 -- -$$ 2>/dev/null
    fi
  done ) &
GUARD=$!
trap "kill $GUARD 2>/dev/null" EXIT
timeout --signal=TERM 138 taskset -c 0,1 "$@"
status=$?
end=$(date +%s.%N)
kill $GUARD 2>/dev/null
rss=$(ps -o rss= -g $$ 2>/dev/null | awk '{s+=$1} END {print s+0}')
wall=$(python3 -c "print(round($end-$start,2))")
rsskb=${rss:-0}
python3 - "$LOG" "$job" "$status" "$wall" "$rsskb" <<'PYEOF'
import json,datetime,sys
log,job,status,wall,rss=sys.argv[1:6]
entry={"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "job":job,"status":int(status),"wall_s":float(wall),"rss_kb":int(rss),
 "caps":{"cpus":2,"cpu_s":120,"wall_s":140,"as_kb":12582912,"rss_guard_kb":6291460,"malloc_arena_max":2}}
open(log,"a").write(json.dumps(entry)+"\n")
PYEOF
exit $status

#!/bin/bash
# Single bounded execution receipt runner for multipartite-ramsey-n3-diagnostic-pi-r2.
# Caps: <=2 CPU affinity, CPU<=120s (script-internal 110s deadline), wall<=140s,
# sampled RSS<=6GiB (recorded), AS ulimit 12GiB, MALLOC_ARENA_MAX=2.
set -u
R2=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/multipartite-ramsey-n3-diagnostic-pi-r2
LOG="$R2/logs"
mkdir -p "$LOG"

{
  echo "utc_start=$(date -u +%FT%T.%N%z)"
  echo "cwd=$(pwd)"
  echo "script=$R2/scripts/dpll.py"
  echo "script_sha256=$(sha256sum "$R2/scripts/dpll.py" | cut -d' ' -f1)"
  echo "python=$(command -v python3) $(python3 -V 2>&1)"
  echo "taskset_cpus=0,1"
  echo "env MALLOC_ARENA_MAX=2"
  echo "ulimit -v (KiB)=12582912"
  echo "wall_cap_s=140 kill_target=process_group"
} > "$LOG/launch-receipt.txt"

# Clean stale group name
rm -f "$LOG/rss-samples.tsv"

( ulimit -v 12582912
  cd "$R2"
  exec taskset -c 0,1 env MALLOC_ARENA_MAX=2 python3 -I -B "$R2/scripts/dpll.py"
) > "$LOG/solver-stdout.txt" 2> "$LOG/solver-stderr.txt" &
PGID=""
PID=$!
PGID=$(ps -o pgid= -p $PID | tr -d ' ')

START=$(date +%s.%N)
while kill -0 "$PID" 2>/dev/null; do
  NOW=$(date +%s.%N)
  ELAPSED=$(echo "$NOW $START" | awk '{printf "%.1f", $1-$2}')
  if [ -f "/proc/$PID/status" ]; then
    RSS=$(awk '/VmRSS/{print $2}' "/proc/$PID/status" 2>/dev/null)
    CPU=$(awk '/^Uid/{next} {print}' /dev/null; cat /proc/$PID/stat 2>/dev/null | awk '{print $14+$15}')
    echo -e "${ELAPSED}\t${RSS:-NA}\t${CPU:-NA}" >> "$LOG/rss-samples.tsv"
  fi
  OVER=$(echo "$ELAPSED 140" | awk '{print ($1>=$2)?1:0}')
  if [ "$OVER" = "1" ]; then
    echo "wall_cap_reached killing pgid=$PGID" >> "$LOG/launch-receipt.txt"
    kill -TERM -- -$PGID 2>/dev/null
    sleep 2
    kill -KILL -- -$PGID 2>/dev/null
    break
  fi
  sleep 1
done
wait "$PID"; EXIT=$?

WALL=$(echo "$(date +%s.%N) $START" | awk '{printf "%.3f", $1-$2}')
{
  echo "utc_end=$(date -u +%FT%T.%N%z)"
  echo "exit_code=$EXIT"
  echo "wall_s=$WALL"
  echo "rss_samples=$( [ -f "$LOG/rss-samples.tsv" ] && wc -l < "$LOG/rss-samples.tsv" || echo 0)"
} >> "$LOG/launch-receipt.txt"

# CPU time of the python process from wait, best effort via times of children already
# captured inside solver-result.json (ru_utime+ru_stime, ru_maxrss).
echo "runner done exit=$EXIT wall=$WALL"
exit 0

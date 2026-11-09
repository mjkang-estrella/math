#!/bin/bash
# ONE guarded full search run. Hard caps:
#   affinity 2 CPUs, total CPU 120s (ulimit -t), wall 140s process-group kill,
#   AS 12GiB (ulimit -v), sampled RSS guard 6GiB, MALLOC_ARENA_MAX=2.
# Every child is in one process group; reaped via wait; sampler reaped too.
set -u
cd "$(dirname "$0")"
mkdir -p logs
export MALLOC_ARENA_MAX=2
SEED=20261105
CPU_BUDGET=112
WALL_DEADLINE=128
PGID=""

cleanup() {
  # reap process group and sampler
  if [ -n "$PGID" ]; then
    kill -TERM -- "-$PGID" 2>/dev/null
    sleep 1
    kill -KILL -- "-$PGID" 2>/dev/null
  fi
  [ -n "$SAMPLER_PID" ] && wait "$SAMPLER_PID" 2>/dev/null
}
trap cleanup EXIT

(
  ulimit -t 120            # hard CPU seconds
  ulimit -v 12582912       # AS 12 GiB
  exec taskset -c 0,1 python3 scripts/search.py \
    --seed $SEED --cpu-budget $CPU_BUDGET --wall-deadline $WALL_DEADLINE
) > logs/search-stdout.txt 2> logs/search-stderr.txt &
CHILD=$!

# own process group for the kill guard
PGID=$(ps -o pgid= -p $CHILD | tr -d ' ')
echo "child_pid=$CHILD pgid=$PGID" > logs/pids.txt

# wall 140s process-group kill + sampled RSS 6GiB guard
(
  START=$(date +%s)
  while kill -0 $CHILD 2>/dev/null; do
    NOW=$(date +%s)
    W=$((NOW - START))
    RSS=$(awk '/VmRSS/{print $2}' /proc/$CHILD/status 2>/dev/null)
    if [ -n "$RSS" ] && [ "$RSS" -gt 6291456 ]; then
      echo "rss_guard_tripped kB=$RSS" >> logs/rss-guard.txt
      kill -KILL -- "-$PGID" 2>/dev/null
      break
    fi
    if [ $W -ge 140 ]; then
      echo "wall_kill_at=${W}s" >> logs/wall-kill.txt
      kill -KILL -- "-$PGID" 2>/dev/null
      break
    fi
    sleep 1
  done
) &
SAMPLER_PID=$!

wait $CHILD
EC=$?
wait $SAMPLER_PID 2>/dev/null
echo "search_exit=$EC" | tee -a logs/pids.txt
exit $EC

#!/usr/bin/env bash
# Capped runner for lane pdtar-review-r1.
# usage: run.sh NAME script.py [args...]
# Caps: 2 CPUs (taskset 0,1), CPU 120 s, address space 6 GiB, wall 140 s,
# MALLOC_ARENA_MAX=2, python3 -I, lane-local TMPDIR and caches.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
NAME="$1"; shift
SCRIPT="$1"; shift
LOG="$LANE/logs/$NAME.log"
REC="$LANE/logs/$NAME.receipt.json"
TIMEF="$LANE/logs/$NAME.time"
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" PYTHONPYCACHEPREFIX="$LANE/cache/pyc"
export RV_SKIP_L1A="${RV_SKIP_L1A:-0}"
export MALLOC_ARENA_MAX=2 OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
START="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
/usr/bin/time -v -o "$TIMEF" timeout 140 taskset -c 0,1 \
  prlimit --cpu=120 --as=6442450944 -- python3 -I "$SCRIPT" "$@" > "$LOG" 2>&1
RC=$?
END="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
MAXRSS="$(grep 'Maximum resident' "$TIMEF" | awk '{print $NF}')"
USER="$(grep 'User time' "$TIMEF" | awk '{print $NF}')"
WALL="$(grep 'Elapsed (wall' "$TIMEF" | awk '{print $NF}')"
cat > "$REC" <<EOF
{"name": "$NAME", "script": "$(basename "$SCRIPT")", "script_sha256": "$(sha256sum "$SCRIPT" | cut -d' ' -f1)",
 "args": "$*", "start_utc": "$START", "end_utc": "$END", "exit_code": $RC,
 "user_cpu_s": "$USER", "wall": "$WALL", "max_rss_kb": "$MAXRSS",
 "caps": "taskset 0,1; prlimit cpu=120 as=6GiB; timeout 140; MALLOC_ARENA_MAX=2; python3 -I",
 "env_RV_SKIP_L1A": "$RV_SKIP_L1A",
 "log_sha256": "$(sha256sum "$LOG" | cut -d' ' -f1)"}
EOF
echo "rc=$RC user=$USER wall=$WALL maxrss_kb=$MAXRSS"
tail -n 40 "$LOG"

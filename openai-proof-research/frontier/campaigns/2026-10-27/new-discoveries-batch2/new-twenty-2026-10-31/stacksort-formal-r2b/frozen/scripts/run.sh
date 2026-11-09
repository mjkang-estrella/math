#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/cache" MALLOC_ARENA_MAX=2 LEAN_NUM_THREADS=1
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD:$PKG/mathlib/.lake/build/lib/lean"
for p in "$PKG"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
CPUS=$(python3 -I -c 'import os; print(",".join(map(str,sorted(os.sched_getaffinity(0))[:2])))')
LOG="$LANE/logs/$(date -u +%Y%m%dT%H%M%S%N).log"
printf '%q ' "$@" > "$LOG"
printf '\n' >> "$LOG"
set +e
(ulimit -c 0; ulimit -t 120; /usr/bin/time -v timeout --kill-after=2 140 taskset -c "$CPUS" python3 -I "$LANE/scripts/bounded.py" "$@") >> "$LOG" 2>&1
RC=$?
printf '\nexit %s\n' "$RC" >> "$LOG"
cat "$LOG"
exit "$RC"

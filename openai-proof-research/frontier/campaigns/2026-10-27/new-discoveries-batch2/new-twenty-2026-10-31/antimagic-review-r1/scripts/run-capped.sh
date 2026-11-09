#!/usr/bin/env bash
# Usage: scripts/run-capped.sh LOGNAME args...   (runs python3 -I scripts/verify.py args)
# Caps: CPU 120 s, wall 140 s, address space 1.5 GiB, MALLOC_ARENA_MAX=2, 2 CPUs.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"; shift
export MALLOC_ARENA_MAX=2 TMPDIR="$LANE/tmp" PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1
cd "$LANE"
(
  ulimit -t 120
  ulimit -v 1572864
  exec timeout 140 taskset -c 0,1 /usr/bin/time -v python3 -I scripts/verify.py "$@"
) > "logs/$name.jsonl" 2> "logs/$name.stderr"
rc=$?
echo "rc=$rc" >> "logs/$name.stderr"
echo "rc=$rc"; grep -E 'Maximum resident|Elapsed' "logs/$name.stderr"; tail -3 "logs/$name.jsonl"

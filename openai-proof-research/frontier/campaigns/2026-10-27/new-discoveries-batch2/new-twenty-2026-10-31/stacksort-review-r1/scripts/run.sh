#!/bin/bash
# Usage: scripts/run.sh <logname> <script.py> [args...]
# Runs ONE capped python3 -I process: 2 CPUs, AS 1.5 GiB, CPU 120 s, wall 140 s.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"; shift
export MALLOC_ARENA_MAX=2 TMPDIR="$LANE/tmp" PYTHONDONTWRITEBYTECODE=1
cd "$LANE"
{
  echo "# utc_start $(date -u +%FT%TZ)"
  echo "# cmd python3 -I $*"
  echo "# script_sha256 $(sha256sum "$1" | cut -d' ' -f1)"
} > "logs/$name.log"
/usr/bin/time -v -o "logs/$name.time" timeout 140 taskset -c 0,1 prlimit --as=1610612736 --cpu=120 python3 -I "$@" >> "logs/$name.log" 2> "logs/$name.stderr"
rc=$?
echo "# exit $rc utc_end $(date -u +%FT%TZ)" >> "logs/$name.log"
grep -E 'Maximum resident|Elapsed|User time|System time' "logs/$name.time" >> "logs/$name.log"
tail -n 40 "logs/$name.log"; cat "logs/$name.stderr" | tail -5

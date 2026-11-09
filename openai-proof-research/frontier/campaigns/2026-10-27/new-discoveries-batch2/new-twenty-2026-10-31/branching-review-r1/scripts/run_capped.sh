#!/usr/bin/env bash
# Capped single-process runner for this review lane (written independently of the discovery lane).
# Usage: run_capped.sh <logname> <script.py> [args...]
# Caps: 2 CPUs (taskset 0,1), CPU 120 s (prlimit), wall 140 s (timeout), address space 1.5 GiB,
# MALLOC_ARENA_MAX=2, python3 -I. Peak RSS and exit status are recorded by /usr/bin/time -v.
set -u
LANE="$(cd "$(dirname "$0")/.." && pwd)"
name="$1"; shift
script="$1"; shift
mkdir -p "$LANE/logs" "$LANE/tmp"
export TMPDIR="$LANE/tmp" MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
log="$LANE/logs/$name.log"
res="$LANE/logs/$name.resources.txt"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ)
cd "$LANE/tmp"
/usr/bin/time -v -o "$res" timeout 140 taskset -c 0,1 \
  prlimit --cpu=120 --as=1610612736 -- python3 -I "$script" "$@" > "$log" 2>&1
rc=$?
end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
{
  echo "start_utc=$start"; echo "end_utc=$end"; echo "exit=$rc"
  echo "script=$script"; echo "args=$*"
  echo "script_sha256=$(sha256sum "$script" | cut -d' ' -f1)"
  echo "log_sha256=$(sha256sum "$log" | cut -d' ' -f1)"
} >> "$res"
echo "exit=$rc"; tail -n 40 "$log"
grep -E 'Maximum resident|Elapsed|User time|System time' "$res"

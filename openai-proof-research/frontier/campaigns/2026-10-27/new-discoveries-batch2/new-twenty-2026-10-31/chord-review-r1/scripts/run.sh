#!/bin/bash
# Capped runner: ONE process, CPU 120 s, wall 140 s, address space ~1.9 GiB, MALLOC_ARENA_MAX=2.
# usage: run.sh <logname> <args to chordrev.py...>
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/chord-review-r1
name=$1; shift
mkdir -p "$R/logs" "$R/tmp"
export TMPDIR="$R/tmp" MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
cd "$R/tmp"
{
  echo "# utc_start $(date -u +%FT%TZ) args: $*"
  ( ulimit -t 120; ulimit -v 1900000; exec timeout 140 /usr/bin/time -v taskset -c 0,1 python3 -I "$R/scripts/chordrev.py" "$@" ) 2>&1
  echo "# exit $? utc_end $(date -u +%FT%TZ)"
} > "$R/logs/$name.log"
grep -v -E '^\s+(Average|Socket|Signals|Swaps|File system|Page size|Voluntary|Involuntary|Minor|Major|Exit status|Percent)' "$R/logs/$name.log" | tail -n 25

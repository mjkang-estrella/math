#!/bin/bash
# Capped single-process runner for this review lane.
# Usage: scripts/run.sh <logname> <script.py> [args...]
# Caps: CPU 120 s (RLIMIT_CPU), wall 140 s (timeout), address space 2 GiB,
# two CPUs (taskset 0,1), MALLOC_ARENA_MAX=2, python3 -I. Peak RSS is recorded by GNU time.
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/middle-review-r1
name=$1; shift
export MALLOC_ARENA_MAX=2 TMPDIR=$R/tmp PYTHONDONTWRITEBYTECODE=1
cd "$R/tmp"
start=$(date -u +%Y-%m-%dT%H:%M:%SZ)
/usr/bin/time -v -o "$R/logs/$name.time" \
  timeout 140 taskset -c 0,1 prlimit --cpu=120 --as=2147483648 \
  python3 -I "$@" > "$R/logs/$name.log" 2> "$R/logs/$name.err"
rc=$?
end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
rss=$(grep 'Maximum resident' "$R/logs/$name.time" | awk '{print $NF}')
cpu_u=$(grep 'User time' "$R/logs/$name.time" | awk '{print $NF}')
cpu_s=$(grep 'System time' "$R/logs/$name.time" | awk '{print $NF}')
printf '{"name":"%s","argv":"%s","start":"%s","end":"%s","exit":%d,"max_rss_kb":%s,"user_s":%s,"sys_s":%s}\n' \
  "$name" "$*" "$start" "$end" "$rc" "${rss:-null}" "${cpu_u:-null}" "${cpu_s:-null}" > "$R/logs/$name.receipt.json"
cat "$R/logs/$name.receipt.json"

#!/usr/bin/env bash
# Capped runner: one python3 -I process, 2 CPUs, CPU 120 s, wall 140 s, AS 3 GiB, MALLOC_ARENA_MAX=2.
# Usage: scripts/run.sh <name> <script.py> [args...]   -> logs/<name>.log, logs/<name>.time
set -u
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/riordan-diameter-review-r1
name=$1; shift
script=$1; shift
export TMPDIR=$L/tmp MALLOC_ARENA_MAX=2 PYTHONDONTWRITEBYTECODE=1
cd $L/tmp
start=$(date -u +%FT%TZ)
( ulimit -t 120; ulimit -v 3145728; exec /usr/bin/time -v -o $L/logs/$name.time \
    timeout 140 taskset -c 0,1 python3 -I $L/scripts/$script "$@" ) > $L/logs/$name.log 2>&1
rc=$?
end=$(date -u +%FT%TZ)
rss=$(grep 'Maximum resident' $L/logs/$name.time | awk '{print $NF}')
cpu=$(grep -E 'User time|System time' $L/logs/$name.time | awk '{s+=$NF} END {print s}')
echo "{\"name\":\"$name\",\"script\":\"$script\",\"args\":\"$*\",\"start\":\"$start\",\"end\":\"$end\",\"rc\":$rc,\"max_rss_kb\":${rss:-null},\"cpu_s\":${cpu:-null},\"script_sha256\":\"$(sha256sum $L/scripts/$script | cut -d' ' -f1)\",\"log_sha256\":\"$(sha256sum $L/logs/$name.log | cut -d' ' -f1)\"}" | tee $L/logs/$name.receipt.json

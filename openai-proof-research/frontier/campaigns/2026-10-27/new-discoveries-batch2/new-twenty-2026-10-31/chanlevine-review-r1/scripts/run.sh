#!/usr/bin/env bash
# Capped runner for ONE python3 -I process: 2 CPUs, ~6 GiB address space, CPU 120 s, wall 140 s.
# Usage: run.sh <label> <script.py> [args...]   (writes logs/<label>.log and logs/<label>.receipt.json)
set -u
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/chanlevine-review-r1
label=$1; shift; script=$1; shift
export TMPDIR=$R/tmp PYTHONDONTWRITEBYTECODE=1 PYTHONPYCACHEPREFIX=$R/tmp/pycache XDG_CACHE_HOME=$R/tmp/cache MALLOC_ARENA_MAX=2 OMP_NUM_THREADS=1
log=$R/logs/$label.log; rec=$R/logs/$label.receipt.json
start=$(date -u +%Y-%m-%dT%H:%M:%SZ); t0=$(date +%s.%N)
( ulimit -t 120; ulimit -v 6291456; cd $R/tmp && exec taskset -c 0,1 timeout -k 5 140 /usr/bin/time -v python3 -I "$script" "$@" ) > "$log" 2> "$log.stderr"
rc=$?
t1=$(date +%s.%N); end=$(date -u +%Y-%m-%dT%H:%M:%SZ)
maxrss=$(grep 'Maximum resident' "$log.stderr" | awk '{print $NF}')
cpu_u=$(grep 'User time' "$log.stderr" | awk '{print $NF}'); cpu_s=$(grep 'System time' "$log.stderr" | awk '{print $NF}')
cat > "$rec" <<JSON
{"label": "$label", "script": "$script", "args": "$*", "script_sha256": "$(sha256sum "$script" | cut -d' ' -f1)",
 "start_utc": "$start", "end_utc": "$end", "wall_s": $(echo "$t1 - $t0" | bc), "user_cpu_s": "${cpu_u:-?}", "sys_cpu_s": "${cpu_s:-?}",
 "max_rss_kb": "${maxrss:-?}", "exit_code": $rc, "log_sha256": "$(sha256sum "$log" | cut -d' ' -f1)", "stderr_sha256": "$(sha256sum "$log.stderr" | cut -d' ' -f1)",
 "caps": "taskset 0,1; ulimit -t 120; ulimit -v 6291456 KiB; timeout 140 s; MALLOC_ARENA_MAX=2; python3 -I"}
JSON
echo "rc=$rc wall=$(echo "$t1 - $t0" | bc) cpu=${cpu_u:-?}+${cpu_s:-?} rss_kb=${maxrss:-?}"; tail -n 40 "$log"

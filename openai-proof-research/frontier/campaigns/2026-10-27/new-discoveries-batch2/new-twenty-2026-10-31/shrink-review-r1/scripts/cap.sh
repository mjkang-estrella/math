#!/bin/bash
# usage: cap.sh LOGNAME cmd args...   (runs one capped process, logs stdout/stderr + receipt)
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/shrink-review-r1
name=$1; shift
export TMPDIR=$L/tmp XDG_CACHE_HOME=$L/tmp/cache PYTHONDONTWRITEBYTECODE=1 MALLOC_ARENA_MAX=2
start=$(date -u +%FT%TZ)
( ulimit -t 120; ulimit -v 6291456; exec timeout 140 taskset -c 0,1 /usr/bin/time -v "$@" ) > $L/logs/$name.log 2> $L/logs/$name.stderr
rc=$?
end=$(date -u +%FT%TZ)
maxrss=$(grep 'Maximum resident' $L/logs/$name.stderr | awk '{print $NF}')
printf '{"name":"%s","cmd":"%s","start":"%s","end":"%s","rc":%d,"maxrss_kb":"%s","caps":"ulimit -t 120, -v 6GiB, timeout 140, taskset 0,1, MALLOC_ARENA_MAX=2"}\n' "$name" "$*" "$start" "$end" $rc "$maxrss" > $L/logs/$name.receipt.json
echo "rc=$rc maxrss_kb=$maxrss"

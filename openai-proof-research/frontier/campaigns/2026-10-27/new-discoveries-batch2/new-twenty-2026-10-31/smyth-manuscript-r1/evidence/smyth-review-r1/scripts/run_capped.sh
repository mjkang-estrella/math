#!/bin/bash
# usage: run_capped.sh NAME script.py [args...]   -- one process, 2 CPUs, CPU 100 s, wall 105 s (tightened after sweep-A8 overran the tool foreground limit), AS 1.5 GiB
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/smyth-review-r1
NAME=$1; shift
export TMPDIR=$L/tmp XDG_CACHE_HOME=$L/cache PYTHONPYCACHEPREFIX=$L/cache/pyc MALLOC_ARENA_MAX=2 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
cd $L
{ echo "# start $(date -u +%FT%TZ) cmd: python3 -I $*"; sha256sum "$1"; } > logs/$NAME.log
/usr/bin/time -v -o logs/$NAME.time timeout -k 3 105 taskset -c 0,1 prlimit --cpu=100 --as=1610612736 python3 -I "$@" >> logs/$NAME.log 2>&1
rc=$?
echo "# end $(date -u +%FT%TZ) rc=$rc" >> logs/$NAME.log
grep -E 'Maximum resident|Elapsed|User time|System time|Exit status' logs/$NAME.time
exit $rc

#!/bin/bash
# Run one guarded command: g.sh LOGNAME cmd...  (stdout/stderr to logs/, never retried)
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-mathdb-circulant-13-source-prior-boundary-r468
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
n=$1; shift
cd $L && OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B $G "$@" > logs/$n.stdout 2> logs/$n.stderr
rc=$?; echo "exit=$rc" >> logs/$n.stderr; cat logs/$n.stdout; tail -2 logs/$n.stderr; exit $rc

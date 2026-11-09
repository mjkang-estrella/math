#!/bin/bash
# guarded arbitrary-command runner
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes
exec env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -I $L/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py "$@"

#!/bin/bash
set -eu
LANE=$(cd -- "$(dirname -- "$0")" && pwd)
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
exec python "$GUARD" python "$LANE/${1:-checks}.py"

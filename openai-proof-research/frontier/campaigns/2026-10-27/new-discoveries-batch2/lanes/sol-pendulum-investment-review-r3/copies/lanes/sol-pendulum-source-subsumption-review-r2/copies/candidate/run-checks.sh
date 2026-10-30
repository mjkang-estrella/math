#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
LANE_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$GUARD" python "$LANE_DIR/analyze.py"
python "$GUARD" python "$LANE_DIR/checks.py"

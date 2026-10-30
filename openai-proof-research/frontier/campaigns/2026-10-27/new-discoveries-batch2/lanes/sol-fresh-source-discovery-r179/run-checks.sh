#!/bin/sh
set -eu
LANE=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r179
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 "$LANE/checks.py" "$@"

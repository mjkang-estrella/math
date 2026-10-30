#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r149
exec python "$L/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$L/checks.py"

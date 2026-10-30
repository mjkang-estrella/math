#!/usr/bin/env bash
set -eu
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
L=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
if [ "${1:-}" = verify ]; then
 python "$G" python "$L/verify.py"
else
 python "$G" python "$L/checks.py" verify
 python "$G" python "$L/newton.py" verify
fi

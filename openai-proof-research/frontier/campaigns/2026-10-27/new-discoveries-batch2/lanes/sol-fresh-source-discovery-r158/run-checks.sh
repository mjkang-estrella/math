#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
GUARD=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$GUARD" python checks.py
python "$GUARD" python ribbon_route.py
python "$GUARD" python finalize.py verify

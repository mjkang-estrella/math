#!/bin/bash
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
if [ "${1:-}" = verify ]; then
 python "$guard" python verify.py
else
 python "$guard" python checks.py
fi

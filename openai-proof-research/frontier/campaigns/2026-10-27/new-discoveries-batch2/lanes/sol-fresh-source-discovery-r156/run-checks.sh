#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python checks.py
python "$guard" python explore.py initial
python "$guard" python explore.py corrected
python "$guard" python control.py

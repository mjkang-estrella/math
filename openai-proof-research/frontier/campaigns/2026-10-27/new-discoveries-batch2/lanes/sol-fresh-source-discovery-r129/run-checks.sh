#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
exec python3 ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 verify.py

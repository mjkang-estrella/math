#!/bin/sh
cd "$(dirname "$0")" || exit 1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 exec python3 -B ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 -B verify.py "$@"

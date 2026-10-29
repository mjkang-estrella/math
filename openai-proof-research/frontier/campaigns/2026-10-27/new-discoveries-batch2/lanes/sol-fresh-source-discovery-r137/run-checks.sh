#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 checks.py

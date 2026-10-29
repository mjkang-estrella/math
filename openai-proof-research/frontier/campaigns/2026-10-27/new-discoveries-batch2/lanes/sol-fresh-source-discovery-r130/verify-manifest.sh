#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
GUARD=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 "$GUARD" python3 work.py verify

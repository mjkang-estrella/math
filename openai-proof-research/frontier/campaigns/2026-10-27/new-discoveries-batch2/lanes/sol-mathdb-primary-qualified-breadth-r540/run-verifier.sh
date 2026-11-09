#!/bin/bash
set -eu
LANE_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B "$LANE_DIR/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$LANE_DIR/verify.py" "$@"

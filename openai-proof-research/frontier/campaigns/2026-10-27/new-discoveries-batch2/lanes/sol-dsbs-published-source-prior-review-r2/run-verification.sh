#!/bin/bash
set -eu
LANE=$(cd -- "$(dirname -- "$0")" && pwd)
GUARD="$LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python "$GUARD" python "$LANE/verify.py" --check-only

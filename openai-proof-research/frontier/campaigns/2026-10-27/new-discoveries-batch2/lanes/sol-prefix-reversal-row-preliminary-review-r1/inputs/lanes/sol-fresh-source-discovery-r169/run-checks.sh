#!/bin/bash
set -eu
TASK_LANE=$(cd "$(dirname "$0")" && pwd)
TASK_GUARD="$TASK_LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
if [ "${1:-}" = verify ]; then
  exec python "$TASK_GUARD" python "$TASK_LANE/verify.py"
fi
python "$TASK_GUARD" python "$TASK_LANE/checks.py"
python "$TASK_GUARD" python "$TASK_LANE/route_checks.py"

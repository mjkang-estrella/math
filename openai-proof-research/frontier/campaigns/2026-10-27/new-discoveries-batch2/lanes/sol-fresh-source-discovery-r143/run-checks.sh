#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
TASK_LANE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
TASK_GUARD="$TASK_LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
python "$TASK_GUARD" python "$TASK_LANE/research.py" checks
python "$TASK_GUARD" python "$TASK_LANE/geometry.py"

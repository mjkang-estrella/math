#!/bin/sh
set -eu
TASK_LANE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 exec python3 -B "$TASK_LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$TASK_LANE/verify.py" "$@"

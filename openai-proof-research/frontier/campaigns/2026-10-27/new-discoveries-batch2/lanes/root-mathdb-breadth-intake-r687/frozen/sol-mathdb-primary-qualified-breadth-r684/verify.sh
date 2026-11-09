#!/bin/sh
set -eu
LANE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B "$LANE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$LANE/verify.py" "$@"

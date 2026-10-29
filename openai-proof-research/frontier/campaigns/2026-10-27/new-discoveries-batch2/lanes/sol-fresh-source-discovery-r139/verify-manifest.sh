#!/bin/sh
set -eu
L=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
exec python "$L/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$L/finalize.py" verify

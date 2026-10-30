#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
L=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python "$L/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$L/finalize.py" verify

#!/bin/bash
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
lane=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
guard="$lane/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
python "$guard" python "$lane/checks.py"
python "$guard" python "$lane/mixed.py"

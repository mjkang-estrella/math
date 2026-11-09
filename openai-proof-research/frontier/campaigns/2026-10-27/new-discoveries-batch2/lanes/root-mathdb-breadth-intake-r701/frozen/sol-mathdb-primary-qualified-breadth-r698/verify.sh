#!/bin/sh
set -eu
lane=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B "$lane/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$lane/verify.py" "$@"

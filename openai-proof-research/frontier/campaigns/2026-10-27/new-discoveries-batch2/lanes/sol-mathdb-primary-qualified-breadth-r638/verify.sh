#!/bin/sh
set -eu
P=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
exec python3 -B "$P/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$P/verify.py" "$@"

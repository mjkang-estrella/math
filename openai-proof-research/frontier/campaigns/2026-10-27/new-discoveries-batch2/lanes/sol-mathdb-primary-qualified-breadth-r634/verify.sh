#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 -B "$HERE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python3 -B "$HERE/verify.py" "$@"

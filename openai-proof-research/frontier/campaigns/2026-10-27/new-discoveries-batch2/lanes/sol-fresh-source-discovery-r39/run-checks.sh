#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
ulimit -v 524288
ulimit -t 50
timeout 60s python3 check.py > check-output.log
timeout 45s python3 independent.py > independent-output.log
timeout 60s python3 cone.py > cone-output.log

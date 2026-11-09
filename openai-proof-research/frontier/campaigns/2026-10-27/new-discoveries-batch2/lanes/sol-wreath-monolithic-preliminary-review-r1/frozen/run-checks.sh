#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
ulimit -v 524288
ulimit -t 25
timeout 40s python3 checks.py

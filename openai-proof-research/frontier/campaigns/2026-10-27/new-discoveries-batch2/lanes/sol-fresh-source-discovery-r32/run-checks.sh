#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
ulimit -v 524288
ulimit -t 45
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
 timeout 35 python check.py
 timeout 50 python probe.py
 timeout 55 python targeted.py

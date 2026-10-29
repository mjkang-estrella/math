#!/bin/bash
set -euo pipefail
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
ulimit -Sv 524288
ulimit -Hv 524288
ulimit -St 20
ulimit -Ht 20
timeout --kill-after=1 30 python independent-check.py

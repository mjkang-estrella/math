#!/bin/bash
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
ulimit -v 524288
ulimit -t 210
exec timeout --signal=TERM --kill-after=2s 230s "$@"

#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
ulimit -v 524288
ulimit -t 55
timeout 30s python reconcile.py
timeout 55s python check.py

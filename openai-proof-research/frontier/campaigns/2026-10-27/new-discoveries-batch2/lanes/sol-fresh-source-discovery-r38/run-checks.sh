#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
timeout 50s python check.py
timeout 50s python probe.py
timeout 50s python probe-high.py

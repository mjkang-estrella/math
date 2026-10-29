#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
python capped_run.py python check.py >check.log 2>check-guard.json
cat check.log check-guard.json
python capped_run.py python turan.py >turan.log 2>turan-guard.json
cat turan.log turan-guard.json

#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
python capped_run.py python check.py transfer > transfer.log 2> transfer-guard.json
python capped_run.py python check.py hankel 1 80 > hankel-1.log 2> hankel-1-guard.json
python capped_run.py python check.py hankel 2 72 > hankel-2.log 2> hankel-2-guard.json
python capped_run.py python bridge_check.py > bridge.log 2> bridge-guard.json

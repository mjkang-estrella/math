#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
python3 capped_run.py python3 exact.py >logs/exact.log 2>logs/exact-guard.json
python3 capped_run.py python3 experiment.py >logs/experiment.log 2>logs/experiment-guard.json
python3 capped_run.py python3 interpolation.py >logs/interpolation.log 2>logs/interpolation-guard.json

#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
for task in check deep routes moments; do
 python capped_run.py python "$task.py" >"$task.log" 2>"$task-guard.json"
 cat "$task-guard.json"
done

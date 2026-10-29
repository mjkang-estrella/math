#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
for n in 3 4 5 6; do
 python capped_run.py python check.py "$n" > "check${n}.log" 2> "check${n}-guard.json"
done
python capped_run.py python routes.py 7 > routes7.log 2> routes7-guard.json
python capped_run.py python independent.py > independent.log 2> independent-guard.json

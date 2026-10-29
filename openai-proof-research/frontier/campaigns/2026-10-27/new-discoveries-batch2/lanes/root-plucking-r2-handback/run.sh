#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
exec prlimit --as=536870912 --cpu=210 -- python3 "$(dirname "$0")/cap.py" "$@"

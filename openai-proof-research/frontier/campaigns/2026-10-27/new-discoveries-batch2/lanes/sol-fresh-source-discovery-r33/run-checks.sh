#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
ulimit -v 524288
ulimit -t 210
python guard.py python check.py
python guard.py python probe.py
python guard.py python targeted.py
python guard.py python hadamard.py
python guard.py python audit.py

#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1
ulimit -v 524288
ulimit -t 175
timeout 200s python check.py > check.log
timeout 130s python verify_independent.py > independent-check.log
timeout 110s python audit_certificate.py > certificate-audit.log

#!/bin/bash
# Regenerate the result table and provenance validation. Expensive searches are listed in SUMMARY.md
# and are rerun individually through scripts/limited.py (each within the lane caps).
set -eu
cd -- "$(dirname -- "$0")"
export PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1
python3 scripts/report.py
python3 scripts/validate.py

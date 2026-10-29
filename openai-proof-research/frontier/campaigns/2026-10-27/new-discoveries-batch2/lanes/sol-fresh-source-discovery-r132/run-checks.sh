#!/usr/bin/env bash
set -euo pipefail
lane=$(cd -- "$(dirname -- "$0")" && pwd)
guard="$lane/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
python3 "$guard" python3 "$lane/checks.py" checks
python3 "$guard" python3 "$lane/work.py" verify

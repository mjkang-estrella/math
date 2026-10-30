#!/bin/sh
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
if [ "${1:-}" = verify ]; then
 exec python "$guard" python verify.py
fi
exec python "$guard" python checks.py

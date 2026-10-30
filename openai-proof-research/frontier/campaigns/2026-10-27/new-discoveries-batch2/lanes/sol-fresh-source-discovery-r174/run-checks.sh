#!/bin/bash
set -eu
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
if [ "${1:-}" = verify ]; then
  exec python "$GUARD" python verify.py
fi
python "$GUARD" python checks.py
python "$GUARD" python diagnostic.py 3 4 5
# Longer optional bounded scan: same unchanged guard, no cap raises.
if [ "${1:-}" = full ]; then
  python "$GUARD" python diagnostic.py 6
fi

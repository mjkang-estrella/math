#!/bin/bash
set -euo pipefail
lane=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 "$guard" python3 "$lane/checks.py"

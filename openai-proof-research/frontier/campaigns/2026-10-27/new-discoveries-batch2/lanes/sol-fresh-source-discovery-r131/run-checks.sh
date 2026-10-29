#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 "$GUARD" python3 games.py > game-check.log 2> game-check-guard.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 "$GUARD" python3 sustain.py > component-check.log 2> component-check-guard.json

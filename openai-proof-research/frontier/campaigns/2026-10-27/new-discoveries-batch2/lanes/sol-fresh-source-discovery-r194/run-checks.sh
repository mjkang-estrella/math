#!/bin/sh
set -eu
cd "$(dirname "$0")"
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py' python checks.py

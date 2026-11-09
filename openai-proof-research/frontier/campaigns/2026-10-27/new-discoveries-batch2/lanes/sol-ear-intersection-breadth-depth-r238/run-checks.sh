#!/bin/bash
set -eu
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
lane="$(cd "$(dirname "$0")" && pwd)"
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python "$lane/mechanisms.py"
python "$guard" python "$lane/breadth_checks.py"
python "$guard" python "$lane/boggle_witness.py"

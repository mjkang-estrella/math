#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python3 "$guard" python3 verify_pins.py
for mod in Definitions Witness; do
  python3 lean_guard.py "$mod.log" -o "$mod.olean" "$mod.lean"
done
python3 lean_guard.py Audit.log Audit.lean
python3 "$guard" python3 audit_verify.py

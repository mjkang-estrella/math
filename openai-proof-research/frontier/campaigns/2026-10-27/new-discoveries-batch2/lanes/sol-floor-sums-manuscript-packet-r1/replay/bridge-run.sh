#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for n in Reduction Symmetry Source Expansion ClipBridge SourceBridge Endpoint; do
 if test -f "$n.olean"; then continue; fi
 until python "$G" python lean_guard.py "logs/$n.log" -o "$n.olean" "$n.lean" >"logs/$n.console" 2>&1; do
  python "$G" python repair.py "$n.lean" || { cat "logs/$n.console"; exit 1; }
 done
 echo "$n OK"
done

#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for f in Audit[0-9]*.lean; do
 n=${f%.lean}
 python "$G" python lean_guard.py "logs/$n.log" "$f" >"logs/$n.console" 2>&1 || { cat "logs/$n.console"; exit 1; }
 echo "$n OK"
done

#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
mkdir -p logs
for f in Reduction.lean Symmetry.lean Source.lean Expansion.lean SemBase.lean Sem[0-9]*.lean Query.lean generated/th_lemma_*.lean Dag[0-9]*.lean; do
 n=${f%.lean}
 if test -f "$n.olean"; then continue; fi
 python "$G" python lean_guard.py "logs/${n//\//_}.log" -o "$n.olean" "$f" >"logs/${n//\//_}.console" 2>&1 || { cat "logs/${n//\//_}.console"; exit 1; }
 echo "$n OK"
done

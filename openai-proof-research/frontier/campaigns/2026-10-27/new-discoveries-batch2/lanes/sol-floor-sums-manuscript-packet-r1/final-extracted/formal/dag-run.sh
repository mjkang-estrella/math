#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for f in Dag[0-9]*.lean; do
 n=${f%.lean}
 if test -f "$n.olean"; then continue; fi
 for mod in $(rg '^import generated\.' "$f" | cut -d' ' -f2); do
  p=${mod//./\/}
  if ! test -f "$p.olean"; then
   python "$G" python lean_guard.py "logs/${p//\//_}.log" -o "$p.olean" "$p.lean" >"logs/${p//\//_}.console" 2>&1 || { cat "logs/${p//\//_}.console"; exit 1; }
  fi
 done
 until python "$G" python lean_guard.py "logs/$n.log" -o "$n.olean" "$f" >"logs/$n.console" 2>&1; do
  python "$G" python repair.py "$f" || { cat "logs/$n.console"; exit 1; }
 done
 echo "$n OK"
done

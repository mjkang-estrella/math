#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build logs tmp cache receipts
sha256sum -c source-manifest.sha256 > logs/manifest.log
binding=$(sha256sum source-manifest.sha256 | cut -d' ' -f1)
while read -r m; do
  receipt="receipts/$m.$binding.ok"
  if [ "${1:-}" = --resume ] && [ -f "$receipt" ] && [ -f "build/$m.olean" ]; then continue; fi
  ./capped.sh lean -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "src/$m.lean" > "logs/$m.lean.log" 2>&1
  ./capped.sh leanchecker "$m" > "logs/$m.leanchecker.log" 2>&1
  touch "$receipt"
  echo "PASS $m"
done < module-order.txt
if rg -n '\b(sorry|admit|axiom|unsafe|partial)\s+(def|theorem|lemma|[A-Z])|\b(sorry|admit|native_decide|ofReduceBool)\b|@\[(implemented_by|extern)' src --glob '*.lean' > logs/source-scan.log; then
  echo 'Inspect forbidden source token' >&2
  exit 1
fi
echo 'PASS all modules, checkers and source scan'

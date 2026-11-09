#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
modules=(AntimagicBasics AntimagicModel AntimagicLabel AntimagicIso AntimagicFinal AntimagicRegression Audit Antimagic2Structure Antimagic2Leaves Antimagic2LowerBound Antimagic2Incidence Antimagic2Star Antimagic2Binary AntimagicFinal2 Antimagic2Audit)
for m in "${modules[@]}"; do
 if [[ ${RESUME:-0} == 1 && -f "build/$m.checked" && "build/$m.checked" -nt "$m.lean" ]]; then continue; fi
 scripts/capped.sh "build-$m" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$m.lean"
 scripts/capped.sh "checker-$m" "$TOOLS/leanchecker" "$m"
 touch "build/$m.checked"
done
sha256sum -c inherited-before.sha256
scripts/capped.sh python-regression python3 -I scripts/regression.py
scripts/capped.sh report2 python3 -I scripts/report2.py

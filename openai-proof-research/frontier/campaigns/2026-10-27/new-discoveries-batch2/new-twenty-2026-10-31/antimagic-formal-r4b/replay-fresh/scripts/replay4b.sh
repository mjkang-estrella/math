#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
sha256sum -c inherited-before.sha256
modules=(AntimagicBasics AntimagicModel AntimagicLabel AntimagicIso AntimagicFinal AntimagicRegression Audit Antimagic2Structure Antimagic2Leaves Antimagic2LowerBound Antimagic2Incidence Antimagic2Star Antimagic2Binary Antimagic2Finite Antimagic2Regression AntimagicFinal2 Antimagic2Audit Antimagic3DepthTwo AntimagicFinal3 Antimagic3Audit Antimagic4BBridge AntimagicFinal4B Antimagic4BAudit)
invalid=0
for m in "${modules[@]}"; do
 digest=$(sha256sum "$m.lean" | cut -d' ' -f1)
 if [[ ${RESUME:-0} == 1 && $invalid == 0 && -f "build/$m.olean" && -f "build/$m.checked" && -f "build/$m.sha256" && $(cat "build/$m.sha256") == "$digest" && $m != Antimagic4BAudit ]]; then continue; fi
 invalid=1
 rm -f "build/$m.checked" "build/$m.sha256"
 scripts/check4b.sh "$m"
 printf '%s\n' "$digest" > "build/$m.sha256"
done
cut -d' ' -f3 inherited-before.sha256 | xargs sha256sum > inherited-after.sha256
cmp inherited-before.sha256 inherited-after.sha256
scripts/capped.sh python-regression python3 -I scripts/regression.py
scripts/capped.sh report4b python3 -I scripts/report4b.py

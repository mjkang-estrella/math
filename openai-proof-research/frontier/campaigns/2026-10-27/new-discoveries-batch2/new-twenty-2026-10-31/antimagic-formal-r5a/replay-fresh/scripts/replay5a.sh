#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
modules=(AntimagicBasics AntimagicModel AntimagicLabel AntimagicIso AntimagicFinal AntimagicRegression Audit Antimagic2Structure Antimagic2Leaves Antimagic2LowerBound Antimagic2Incidence Antimagic2Star Antimagic2Binary Antimagic2Finite Antimagic2Regression AntimagicFinal2 Antimagic2Audit Antimagic3DepthTwo AntimagicFinal3 Antimagic3Audit Antimagic4AHigh Antimagic4ABijection Antimagic4ADepthTwo Antimagic4ALeafBlocks Antimagic4AShell AntimagicFinal4A Antimagic4AAudit Antimagic5AShellRows Antimagic5AInternal Antimagic5ALeafParameters Antimagic5ARowSums Antimagic5AVertices Antimagic5ALeafRow Antimagic5ABijection AntimagicFinal5A Antimagic5AAudit)
for m in "${modules[@]}"; do
 if [[ ${RESUME:-0} == 1 && -f "build/$m.checked" && "build/$m.checked" -nt "$m.lean" ]]; then continue; fi
 scripts/capped.sh "build-$m" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$m.lean"
 scripts/capped.sh "checker-$m" "$TOOLS/leanchecker" "$m"
 touch "build/$m.checked"
done
while read -r digest name; do sha256sum "$name"; done < inherited-before.sha256 > inherited-after.sha256
cmp inherited-before.sha256 inherited-after.sha256
scripts/capped.sh python-regression python3 -I scripts/regression.py
scripts/capped.sh grid5a python3 -I scripts/grid5a.py
scripts/capped.sh report5a python3 -I scripts/report5a.py

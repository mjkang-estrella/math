#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
# One Lean/checker process at a time. RESUME trusts only markers made by this driver.
RESUME=${RESUME:-0} bash scripts/build-base.sh
for m in Antimagic7AParameters Antimagic7ALeaves Antimagic7ABijection Antimagic7AWeights Antimagic7AConstruction Antimagic4BBridge AntimagicFinal4B AntimagicFinal7A Antimagic7AAudit; do
 if [[ ${RESUME:-0} == 1 && -f "build/$m.checked" && "build/$m.checked" -nt "$m.lean" ]]; then continue; fi
 bash scripts/check7a.sh "$m"
 touch "build/$m.checked"
done
sha256sum -c inherited-before.sha256
while read -r digest name; do sha256sum "$name"; done < inherited-before.sha256 > inherited-after.sha256
cmp inherited-before.sha256 inherited-after.sha256
scripts/capped.sh python-regression python3 -I scripts/regression.py
scripts/capped.sh grid5a python3 -I scripts/grid5a.py
scripts/capped.sh grid6a python3 -I scripts/grid6a.py
scripts/capped.sh grid7a python3 -I scripts/grid7a.py
scripts/capped.sh report7a python3 -I scripts/report7a.py

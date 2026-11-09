#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
mkdir -p logs tmp cache
stamp=$(date +%s%N)
bash scripts/validate.sh > "logs/replay-root-$stamp.log" 2>&1
bash scripts/controls.sh > "logs/controls-root-$stamp.log" 2>&1
scripts/capped.sh python3 -I scripts/regression7.py
sha256sum -c inherited-before.sha256 > "logs/hashes-$stamp.log"
while read -r digest name; do sha256sum "$name"; done < inherited-before.sha256 > inherited-after.sha256
cmp inherited-before.sha256 inherited-after.sha256
scripts/capped.sh python3 -I scripts/package7.py
if [[ ! -d fresh-extraction ]]; then scripts/capped.sh python3 -I scripts/extract7.py; fi
# Refuse stale extracted sources rather than silently validating a different packet.
for f in src/*.lean; do cmp "$f" "fresh-extraction/$f"; done
(cd fresh-extraction && bash scripts/validate.sh) > "logs/replay-fresh-$stamp.log" 2>&1
(cd fresh-extraction && bash scripts/controls.sh) > "logs/controls-fresh-$stamp.log" 2>&1
scripts/capped.sh python3 -I scripts/finalize7.py
scripts/capped.sh python3 -I scripts/package7.py

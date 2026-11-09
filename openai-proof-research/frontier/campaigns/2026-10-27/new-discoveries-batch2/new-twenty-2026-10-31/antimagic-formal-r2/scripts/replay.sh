#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p build logs tmp cache
for m in AntimagicBasics AntimagicModel AntimagicLabel AntimagicIso AntimagicFinal AntimagicRegression Audit; do
 scripts/capped.sh "build-$m" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$m.lean"
 scripts/capped.sh "checker-$m" "$TOOLS/leanchecker" "$m"
done
scripts/capped.sh python python3 -I scripts/regression.py
scripts/capped.sh report python3 -I scripts/report.py

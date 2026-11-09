#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
m=${1:?explicit module required}
scripts/capped.sh "build-$m" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$m.lean"
scripts/capped.sh "checker-$m" "$TOOLS/leanchecker" "$m"
touch "build/$m.checked"

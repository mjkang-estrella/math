#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")/.."
source scripts/env.sh
m=$1
scripts/capped.sh "build-$m" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$m.lean"
scripts/capped.sh "checker-$m" "$TOOLS/leanchecker" "$m"

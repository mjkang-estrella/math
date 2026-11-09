#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
scripts/capped.sh "$1" "$TOOLS/lean" -j1 -M3500 -DwarningAsError=true -o "build/$1.olean" "$1.lean"

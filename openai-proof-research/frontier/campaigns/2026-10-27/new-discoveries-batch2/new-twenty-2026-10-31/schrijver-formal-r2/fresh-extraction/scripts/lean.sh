#!/bin/bash
set -euo pipefail
LANE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd :)"
cd "$LANE/src"
exec "$LANE/scripts/cap.sh" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 -DwarningAsError=true "$@"

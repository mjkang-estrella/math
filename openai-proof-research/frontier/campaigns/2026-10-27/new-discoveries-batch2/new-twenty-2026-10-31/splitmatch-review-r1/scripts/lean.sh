#!/bin/bash
set -eu
L=$(cd "$(dirname "$0")/.." && pwd)
T=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
F=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal
export LEAN_PATH="$L/build:$(find "$F/.lake/packages" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
export PATH="$L/scripts/bin:$T:$PATH"
cd "$L/build"
if [ "$1" = checker ]; then exec "$T/leanchecker" SplitMatching; fi
exec "$T/lean" -j1 -M3500 -DwarningAsError=true "$@"

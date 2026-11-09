#!/bin/bash
set -eu
D=$(cd "$(dirname "$0")/.." && pwd)
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$(pwd):"$(find "$P" -type d -path '*/.lake/build/lib/lean' -print | paste -sd:)
exec timeout 140 python "$D/scripts/limited.py" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -DwarningAsError=true "$@"

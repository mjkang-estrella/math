#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
M=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD"
for p in "$M"/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$p"; done
exec "$L/scripts/cap.sh" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M3500 -DwarningAsError=true "$@"

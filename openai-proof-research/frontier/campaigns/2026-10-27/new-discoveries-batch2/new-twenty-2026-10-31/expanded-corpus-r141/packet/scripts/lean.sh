#!/bin/bash
set -eu
base=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$(find "$base" -maxdepth 4 -type d -path '*/.lake/build/lib' | paste -sd:):$base/mathlib/.lake/build/lib/lean:$PWD/formal"
# Package build directories use lib/lean.
for p in "$base"/*/.lake/build/lib/lean; do export LEAN_PATH="$p:$LEAN_PATH"; done
exec ./scripts/run-capped.sh /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -M3500 "$@"

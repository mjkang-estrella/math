#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
packages=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD/formal"
for d in "$packages"/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$d"
done
lean=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
if (( $# )); then
  "$lean" -DwarningAsError=true "$@"
else
  "$lean" -DwarningAsError=true -o formal/RealRatios.olean formal/RealRatios.lean
  "$lean" -DwarningAsError=true -o formal/ArithmeticRatios.olean formal/ArithmeticRatios.lean
  "$lean" -DwarningAsError=true formal/Checks.lean
fi

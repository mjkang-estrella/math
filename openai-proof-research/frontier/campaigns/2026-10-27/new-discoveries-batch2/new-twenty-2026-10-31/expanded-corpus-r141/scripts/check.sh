#!/bin/bash
set -eu
export PATH="$PWD/scripts/toolbin":/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
base=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD/formal"
for p in "$base"/*/.lake/build/lib/lean; do export LEAN_PATH="$p:$LEAN_PATH"; done
exec ./scripts/run-capped.sh /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker "$@"

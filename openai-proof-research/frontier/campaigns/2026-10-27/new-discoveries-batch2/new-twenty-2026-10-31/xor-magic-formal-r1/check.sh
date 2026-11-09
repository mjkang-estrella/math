#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
export PATH="/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin"
export LEAN_PATH="$PWD/formal"
for pkg in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*; do
 export LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"
done
export TMPDIR="$PWD"
exec python3 -I tools/bounded.py "$1" leanchecker --verbose "${@:2}"

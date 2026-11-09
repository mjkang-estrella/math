#!/bin/bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
ROOT=/home/mj-kang/Documents/Dev/math
BIN="$ROOT/dlp-research/.tools/lean-4.34.1-linux/bin"
export PATH="$BIN:$PATH"
export LEAN_SYSROOT="$BIN/.." LEAN_NUM_THREADS=1
PKG="$ROOT/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages"
export LEAN_PATH="$LANE/build:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
exec "$LANE/scripts/run.sh" "$BIN/${LEAN_TOOL:-lean}" -j1 -M3500 -DwarningAsError=true "$@"

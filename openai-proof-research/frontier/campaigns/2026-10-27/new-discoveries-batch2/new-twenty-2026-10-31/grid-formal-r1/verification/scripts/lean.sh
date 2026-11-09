#!/bin/bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
ROOT=/home/mj-kang/Documents/Dev/math
BIN="$ROOT/dlp-research/.tools/lean-4.34.1-linux/bin"
PKG="$ROOT/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages"
export PATH="$BIN:$PATH"
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp" MALLOC_ARENA_MAX=2
export LEAN_PATH="$LANE/build:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
ulimit -t 120
ulimit -c 0
exec python3 "$LANE/scripts/limit.py" taskset -c 0,1 timeout -k 2 140 "$BIN/${LEAN_TOOL:-lean}" -j1 -M3500 -DwarningAsError=true "$@"

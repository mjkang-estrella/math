#!/bin/bash
set -eu
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$1:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export PATH="$BIN:$PATH"
TOOL=$2; shift 2
if [ "$TOOL" = lean ]; then exec "$BIN/lean" -j1 -M3500 -DwarningAsError=true "$@"; fi
exec "$BIN/leanchecker" "$@"

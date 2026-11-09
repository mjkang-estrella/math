#!/bin/bash
set -eu
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$PWD/lean:$(find "$PKG" -path '*/.lake/build/lib/lean' -type d | paste -sd:)"
exec /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j2 -M3500 -DwarningAsError=true "$@"

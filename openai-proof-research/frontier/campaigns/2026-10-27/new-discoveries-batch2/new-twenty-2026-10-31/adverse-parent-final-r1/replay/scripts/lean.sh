#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
LEAN_BIN=${LEAN_BIN:-/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin}
LEAN_PACKAGES=${LEAN_PACKAGES:-/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages}
LEAN_PATH="$HERE/formal"
for pkg in "$LEAN_PACKAGES"/*; do
 if [ -d "$pkg/.lake/build/lib/lean" ]; then LEAN_PATH="$LEAN_PATH:$pkg/.lake/build/lib/lean"; fi
done
export LEAN_PATH
LABEL=$1
shift
exec python3 -I "$HERE/scripts/bounded.py" "$LABEL" "$LEAN_BIN/lean" -j1 -DwarningAsError=true "$@"

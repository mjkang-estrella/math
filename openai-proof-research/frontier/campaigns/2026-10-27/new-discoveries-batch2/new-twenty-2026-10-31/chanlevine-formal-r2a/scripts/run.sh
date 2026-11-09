#!/bin/bash
set -euo pipefail
lane=$(cd "$(dirname "$0")/.." && pwd)
export PATH="/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH"
export XDG_CACHE_HOME="$lane/tmp/cache"
export TMPDIR="$lane/tmp" MALLOC_ARENA_MAX=2
export LEAN_PATH="$lane/formal"
pkgs=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
for d in "$pkgs"/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$d"; done
log=$(mktemp "$lane/logs/run-XXXXXXXX.log")
printf '%s\n' "$log"
/usr/bin/time -v python3 -I "$lane/scripts/cap.py" "$@" >"$log" 2>&1 || { cat "$log"; exit 1; }
cat "$log"

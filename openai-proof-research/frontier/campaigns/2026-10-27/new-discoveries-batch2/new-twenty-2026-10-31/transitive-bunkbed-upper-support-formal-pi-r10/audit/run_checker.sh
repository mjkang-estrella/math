#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
export PATH="$LEAN_BIN:$PATH"
export LEAN_PATH="$LANE/build"
exec timeout 140 python3 -I -B "$LANE/runner.py" "leanchecker_UpperSupport" -- \
  "$LEAN_BIN/leanchecker" "$LANE/build/BunUpperSupport.olean"

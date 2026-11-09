#!/bin/bash
# Compile one module with strict caps; propagate real exit status. NO || true.
# Usage: check.sh Module [extra lean args...]
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
PACK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build:$PACK/mathlib/.lake/build/lib/lean:$PACK/batteries/.lake/build/lib/lean:$PACK/aesop/.lake/build/lib/lean:$PACK/Qq/.lake/build/lib/lean:$PACK/proofwidgets/.lake/build/lib/lean:$PACK/importGraph/.lake/build/lib/lean:$PACK/LeanSearchClient/.lake/build/lib/lean:$PACK/plausible/.lake/build/lib/lean"
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
m=$1; shift
exec "$LANE/scripts/run.sh" "lean_$m" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true \
  -o "$LANE/build/$m.olean" "$LANE/src/$m.lean" "$@"

#!/bin/bash
# r6 strict build wrapper. Caps and receipts live entirely in runner.py
# (python3 -I -B). Outer `timeout 140` is a catastrophe backstop, NOT the
# enforced cap (runner enforces dev-guard 130 / wall 140 group kill itself).
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
PACK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/crown-fullside-ideal-formal-pi-r13/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/crown-cut-classification-formal-pi-r11/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/crown-cut-families-formal-pi-r10/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/crown-cut-bridge-formal-pi-r9/build:/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/crown-vnumber-formal-pi-r7/build:$PACK/mathlib/.lake/build/lib/lean:$PACK/batteries/.lake/build/lib/lean:$PACK/aesop/.lake/build/lib/lean:$PACK/Qq/.lake/build/lib/lean:$PACK/proofwidgets/.lake/build/lib/lean:$PACK/importGraph/.lake/build/lib/lean:$PACK/LeanSearchClient/.lake/build/lib/lean:$PACK/plausible/.lake/build/lib/lean"
LEAN_BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
m=$1; shift
exec timeout 140 python3 -I -B "$LANE/runner.py" "lean_$m" -- \
  "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true \
  -o "$LANE/build/$m.olean" "$LANE/src/$m.lean" "$@"

#!/bin/bash
set -eu
CR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
LANE=$(dirname "$CR"); source "$LANE/env.sh"
# override LEAN_PATH: cleanroom build + pinned upstream only
PACK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$CR/build:$PACK/mathlib/.lake/build/lib/lean:$PACK/batteries/.lake/build/lib/lean:$PACK/aesop/.lake/build/lib/lean:$PACK/Qq/.lake/build/lib/lean:$PACK/proofwidgets/.lake/build/lib/lean:$PACK/importGraph/.lake/build/lib/lean:$PACK/LeanSearchClient/.lake/build/lib/lean:$PACK/plausible/.lake/build/lib/lean"
m=$1; shift
exec timeout 140 python3 -I -B "$LANE/runner.py" "cleanroom_lean_$m" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$CR/build/$m.olean" "$CR/src/$m.lean" "$@"

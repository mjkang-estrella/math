#!/bin/bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$LANE"
mkdir -p logs tmp build
RUN="$(date -u +%Y%m%dT%H%M%S)-$$"
scripts/run.sh python3 scripts/prep.py > "logs/$RUN-prep.log" 2>&1
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
scripts/lean.sh "--root=$PKG/mathlib" -o build/Mathlib/Tactic/Bound/Attribute.olean "$PKG/mathlib/Mathlib/Tactic/Bound/Attribute.lean" > "logs/$RUN-Attribute.log" 2>&1
MODS="GridBasic GridSymmetry GridFinal GridChecks GridRegression Audit GridPropagation GridNeighbours GridLattice GridDeterminism GridTransport GridFinal2 Audit2 GridFiniteCodes GridExceptionalPartitions GridExceptionalTwo GridExceptionalCounts GridExceptionalCountTwo GridExceptionalSubgroups GridExceptional GridFreePaths GridFinal3 Audit3"
for M in $MODS; do
  HASH="$(sha256sum "src/$M.lean" | cut -d' ' -f1)"
  if [ ! -f "build/$M.replay-ok" ] || [ "$(cat "build/$M.replay-ok")" != "$HASH" ]; then
    scripts/lean.sh --root=src -o "build/$M.olean" "src/$M.lean" > "logs/$RUN-compile-$M.log" 2>&1
    LEAN_TOOL=leanchecker scripts/lean.sh "$M" > "logs/$RUN-checker-$M.log" 2>&1
    echo "$HASH" > "build/$M.replay-ok"
  fi
  echo "PASS $M"
done
for F in controls/*.lean; do
  if scripts/lean.sh "$F" > "logs/$RUN-negative-$(basename "$F").log" 2>&1; then
    echo "Unexpected success $F"; exit 1
  fi
  echo "EXPECTED_FAILURE $F"
done

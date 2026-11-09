#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$LANE/env.sh"
UPSTREAM=${LEAN_PATH#*:}
UPSTREAM=${UPSTREAM#*:}
UPSTREAM=${UPSTREAM#*:}
export LEAN_PATH="$LANE/cleanroom/build:$UPSTREAM"
python3 -I -B "$LANE/runner.py" clean_PolynexusDiag -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusDiag.olean" "$LANE/cleanroom/src/PolynexusDiag.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusDiag -- "$LEAN_BIN/leanchecker" PolynexusDiag
python3 -I -B "$LANE/runner.py" clean_PolynexusSrc -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusSrc.olean" "$LANE/cleanroom/src/PolynexusSrc.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusSrc -- "$LEAN_BIN/leanchecker" PolynexusSrc
python3 -I -B "$LANE/runner.py" clean_PolynexusProd -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusProd.olean" "$LANE/cleanroom/src/PolynexusProd.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusProd -- "$LEAN_BIN/leanchecker" PolynexusProd
python3 -I -B "$LANE/runner.py" clean_PolynexusClose -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusClose.olean" "$LANE/cleanroom/src/PolynexusClose.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusClose -- "$LEAN_BIN/leanchecker" PolynexusClose
python3 -I -B "$LANE/runner.py" clean_PolynexusSrcPrd -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusSrcPrd.olean" "$LANE/cleanroom/src/PolynexusSrcPrd.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusSrcPrd -- "$LEAN_BIN/leanchecker" PolynexusSrcPrd
python3 -I -B "$LANE/runner.py" clean_PolynexusPairs -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusPairs.olean" "$LANE/cleanroom/src/PolynexusPairs.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusPairs -- "$LEAN_BIN/leanchecker" PolynexusPairs
python3 -I -B "$LANE/runner.py" clean_PolynexusCount -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusCount.olean" "$LANE/cleanroom/src/PolynexusCount.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusCount -- "$LEAN_BIN/leanchecker" PolynexusCount
python3 -I -B "$LANE/runner.py" clean_PolynexusPartition -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusPartition.olean" "$LANE/cleanroom/src/PolynexusPartition.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusPartition -- "$LEAN_BIN/leanchecker" PolynexusPartition
python3 -I -B "$LANE/runner.py" clean_PolynexusGap -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusGap.olean" "$LANE/cleanroom/src/PolynexusGap.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusGap -- "$LEAN_BIN/leanchecker" PolynexusGap
python3 -I -B "$LANE/runner.py" clean_PolynexusGapCount -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusGapCount.olean" "$LANE/cleanroom/src/PolynexusGapCount.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusGapCount -- "$LEAN_BIN/leanchecker" PolynexusGapCount
python3 -I -B "$LANE/runner.py" clean_PolynexusEval -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusEval.olean" "$LANE/cleanroom/src/PolynexusEval.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusEval -- "$LEAN_BIN/leanchecker" PolynexusEval
python3 -I -B "$LANE/runner.py" clean_PolynexusLiteral -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/build/PolynexusLiteral.olean" "$LANE/cleanroom/src/PolynexusLiteral.lean"
python3 -I -B "$LANE/runner.py" cleanchecker_PolynexusLiteral -- "$LEAN_BIN/leanchecker" PolynexusLiteral
python3 -I -B "$LANE/runner.py" clean_deep_audit -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true "$LANE/audit/Deep.lean"

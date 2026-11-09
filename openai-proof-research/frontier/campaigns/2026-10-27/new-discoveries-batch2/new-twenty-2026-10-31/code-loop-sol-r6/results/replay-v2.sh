#!/bin/bash
set -eu
LANE=$(pwd)
source "$LANE/env.sh"
export LEAN_PATH="$LANE/cleanroom/source-replay-v2/build:${LEAN_PATH#*:}"
for m in CodeLoopFactor CodeLoopCount CodeLoopSets CodeLoopGeom CodeLoopCodes CodeLoopSpace CodeLoopWeight CodeLoopLoop CodeLoopClasses CodeLoopIntersections CodeLoopRepresentations CodeLoopSigns CodeLoopLiteral CodeLoopFin50 CodeLoopTransport; do
  python3 -I -B "$LANE/runner.py" "replay_v2_$m" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/source-replay-v2/build/$m.olean" "$LANE/cleanroom/source-replay-v2/src/$m.lean"
done

#!/bin/bash
set -eu
LANE=$(pwd)
source "$LANE/env.sh"
export LEAN_PATH="$LANE/cleanroom/source-replay/build:${LEAN_PATH#*:}"
for m in CodeLoopFactor CodeLoopCount CodeLoopSets CodeLoopGeom CodeLoopCodes CodeLoopSpace CodeLoopWeight CodeLoopLoop CodeLoopClasses CodeLoopIntersections CodeLoopRepresentations CodeLoopSigns CodeLoopLiteral CodeLoopFin50; do
  python3 -I -B "$LANE/runner.py" "replay_$m" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/cleanroom/source-replay/build/$m.olean" "$LANE/cleanroom/source-replay/src/$m.lean"
done

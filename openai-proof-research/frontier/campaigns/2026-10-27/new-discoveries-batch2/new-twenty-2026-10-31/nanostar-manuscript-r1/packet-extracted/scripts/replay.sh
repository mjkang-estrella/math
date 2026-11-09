#!/bin/bash
set -eu
D=$(cd "$(dirname "$0")/.." && pwd)
R=$D/replay
"$D/scripts/run" replay-extract python3 -I "$D/scripts/extract-replay.py"
export TASK_LEAN_DIR="$R"
for m in Definitions Arithmetic Certificate EdgeRows0 EdgeRows1 EdgeRows2 EdgeRows3 EdgeRows4 EdgeRows5 EdgeRows6 EdgeRows7 Endpoint; do
 "$D/scripts/run" "replay-$m" "$D/scripts/lean-env" -DwarningAsError=true -o "$R/$m.olean" "$R/$m.lean"
 "$D/scripts/run" "leanchecker-$m" "$D/scripts/check-env" "$m"
done

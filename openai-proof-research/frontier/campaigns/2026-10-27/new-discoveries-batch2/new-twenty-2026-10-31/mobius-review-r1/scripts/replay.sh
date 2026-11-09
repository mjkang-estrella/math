#!/bin/bash
set -eu
D=$(cd -- "$(dirname -- "$0")/.." && pwd)
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH LEAN_PATH="$D/replay/fresh" LEAN_NUM_THREADS=2
cd "$D/replay/fresh"
"$D/scripts/cap.sh" lean -j2 -M3500 -DwarningAsError=true -o Mobius.olean Mobius.lean > "$D/logs/build.log" 2>&1
"$D/scripts/cap.sh" leanchecker Mobius > "$D/logs/checker.log" 2>&1
"$D/scripts/cap.sh" lean -j2 -M3500 -DwarningAsError=true Audit.lean > "$D/logs/audit.log" 2>&1

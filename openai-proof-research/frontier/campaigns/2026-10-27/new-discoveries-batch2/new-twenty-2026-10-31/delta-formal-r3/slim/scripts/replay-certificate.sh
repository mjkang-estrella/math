#!/bin/bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
source "$HERE/scripts/env.sh"
export LEAN_PATH="$HERE/build:${LEAN_PATH#*:}"
cd "$HERE"
mkdir -p build logs/replay "$LANE/tmp" "$LANE/cache"
for n in $(seq "${1:-108}" "${2:-581}"); do
 module=$(printf 'Closure%03d' "$n")
 scripts/cap.sh lean -j2 -M3500 -DwarningAsError=true -o "build/$module.olean" "lean/$module.lean" > "logs/replay/$module.lean.log" 2>&1
 scripts/cap.sh leanchecker "$module" > "logs/replay/$module.checker.log" 2>&1
 touch "logs/replay/$module.ok"
 echo "Replayed $module"
 if [[ -f "$LANE/STOP_REPLAY" ]]; then echo "Controlled boundary stop after $module"; exit 75; fi
done

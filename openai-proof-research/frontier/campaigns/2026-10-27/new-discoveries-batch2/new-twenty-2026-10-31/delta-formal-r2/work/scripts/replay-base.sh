#!/bin/bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
source "$HERE/scripts/env.sh"
export LEAN_PATH="$HERE/build:${LEAN_PATH#*:}"
mkdir -p "$HERE/build" "$HERE/logs/replay" "$LANE/tmp" "$LANE/cache"
cd "$HERE"
while read -r module; do
 [[ -n "$module" ]] || continue
 if [[ "${1:-}" == --resume && -f "logs/replay/$module.ok" && "build/$module.olean" -nt "lean/$module.lean" ]]; then continue; fi
 "$HERE/scripts/cap.sh" lean -M3500 -DwarningAsError=true -o "build/$module.olean" "lean/$module.lean" > "logs/replay/$module.lean.log" 2>&1
 "$HERE/scripts/cap.sh" leanchecker "$module" > "logs/replay/$module.checker.log" 2>&1
 touch "logs/replay/$module.ok"
 echo "Replayed $module"
done < base-modules.txt

#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
# Use a new lane-local extraction for each independent replay. Resuming preserves
# prior successful artifacts in this extraction; fresh default rebuilds all modules.
ROOT="${1:-$LANE/replay-final}"
case "$ROOT" in "$LANE"/*) ;; *) echo 'Extraction must remain lane-local' >&2; exit 2;; esac
mkdir -p "$ROOT"
if [ ! -f "$ROOT/module-order.txt" ]; then unzip -q "$LANE/source-only.zip" -d "$ROOT"; fi
mkdir -p "$ROOT/build" "$ROOT/logs"
export LEAN_PATH="$ROOT/build:${LEAN_PATH#*:}"
while read -r m; do
 if [ "${RESUME:-0}" = 1 ] && [ -f "$ROOT/logs/$m.PASS" ]; then continue; fi
 cap lean -M3500 -DwarningAsError=true -o "$ROOT/build/$m.olean" "$ROOT/src/$m.lean" > "$ROOT/logs/$m.lean.log" 2>&1
 cap leanchecker "$m" > "$ROOT/logs/$m.checker.log" 2>&1
 touch "$ROOT/logs/$m.PASS"
 echo "$m strict compile and explicit-module checker PASS"
done < "$ROOT/module-order.txt"

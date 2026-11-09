#!/bin/bash
set -euo pipefail
source "$(dirname "$0")/env.sh"
ROOT="${1:-$LANE/replay-final}"
case "$ROOT" in "$LANE"/*) ;; *) exit 2;; esac
if [ "${RESUME:-0}" != 1 ] && [ -e "$ROOT" ]; then echo 'Fresh replay needs an unused path'; exit 2; fi
mkdir -p "$ROOT"
if [ ! -f "$ROOT/module-order.txt" ]; then unzip -q "$LANE/source-only.zip" -d "$ROOT"; fi
mkdir -p "$ROOT/build" "$ROOT/logs"
export LEAN_PATH="$ROOT/build:${LEAN_PATH#*:}"
while IFS= read -r m; do
 if [ "${RESUME:-0}" = 1 ] && [ -f "$ROOT/logs/$m.PASS" ]; then continue; fi
 cap lean -M3500 -DwarningAsError=true -o "$ROOT/build/$m.olean" "$ROOT/src/$m.lean" > "$ROOT/logs/$m.lean.log" 2>&1
 cap leanchecker "$m" > "$ROOT/logs/$m.checker.log" 2>&1
 touch "$ROOT/logs/$m.PASS"
 echo "$m PASS"
done < "$ROOT/module-order.txt"

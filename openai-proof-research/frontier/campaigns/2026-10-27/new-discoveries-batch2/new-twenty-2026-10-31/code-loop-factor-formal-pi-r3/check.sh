#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$LANE/env.sh"
m=$1; shift
exec timeout 140 python3 -I -B "$LANE/runner.py" "lean_$m" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/build/$m.olean" "$LANE/src/$m.lean" "$@"

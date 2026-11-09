#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$LANE/env.sh"
exec timeout 140 python3 -I -B "$LANE/runner.py" "audit_$1" -- "$LEAN_BIN/lean" -j1 -M3500 -DwarningAsError=true "$LANE/audit/$1.lean"

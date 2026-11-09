#!/bin/bash
set -eu
LANE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$LANE/env.sh"
m=$1
exec timeout 140 python3 -I -B "$LANE/runner.py" "leanchecker_$m" -- "$LEAN_BIN/leanchecker" "$m"

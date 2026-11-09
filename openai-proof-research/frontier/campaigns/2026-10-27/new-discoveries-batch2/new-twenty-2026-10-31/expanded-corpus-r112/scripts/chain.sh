#!/bin/bash
# sequential capped calls: each argument is "logname|spec"
cd "$(dirname "$0")/.."
for item in "$@"; do name=${item%%|*}; spec=${item#*|}; python3 -I scripts/limited.py "$name" python3 -I scripts/ramsey_cells.py "$name" 112 $spec; done

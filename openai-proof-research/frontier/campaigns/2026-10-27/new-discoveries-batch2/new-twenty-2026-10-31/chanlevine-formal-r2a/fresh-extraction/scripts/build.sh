#!/bin/bash
set -euo pipefail
lane=$(cd "$(dirname "$0")/.." && pwd)
cd "$lane/formal"
for mod in "$@"; do
 bash "$lane/scripts/run.sh" lean -j1 -M3500 -DwarningAsError=true -o "$mod.olean" "$mod.lean"
done

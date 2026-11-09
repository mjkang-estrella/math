#!/bin/bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")/.." && pwd)
source "$HERE/scripts/env.sh"
export LEAN_PATH="$HERE/build:${LEAN_PATH#*:}"
cd "$HERE"
module=$1
mkdir -p logs/development
scripts/cap.sh lean -j2 -M3500 -DwarningAsError=true -o "build/$module.olean" "lean/$module.lean" > "logs/development/$module.lean.log" 2>&1
scripts/cap.sh leanchecker "$module" > "logs/development/$module.checker.log" 2>&1

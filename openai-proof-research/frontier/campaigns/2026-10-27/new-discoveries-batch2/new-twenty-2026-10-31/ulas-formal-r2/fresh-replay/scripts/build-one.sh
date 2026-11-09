#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
cd "$L/src"
bash "$L/scripts/run.sh" "$1-$(date +%s%N)" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 -DwarningAsError=true -o "$L/build/$1.olean" "$1.lean"

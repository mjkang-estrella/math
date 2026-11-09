#!/bin/bash
# usage: lean/run.sh File.lean [olean]   (run from lean/), RSS-capped at 6 GiB, CPU 120 s, wall 140 s, 2 threads
cd "$(dirname "$0")"; source ./env.sh; export LEAN_PATH=$LEAN_PATH:$(pwd)/build
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
if [ -n "$2" ]; then OUT=(-o "build/$2"); else OUT=(); fi
python3 ../scripts/rsscap.py 6144 140 120 -- $LEAN -j2 -DwarningAsError=true "${OUT[@]}" "$1"

#!/bin/bash
set -eu
cd "$(dirname "$0")"
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
mkdir -p build
export LEAN_PATH="$PWD/build"
while read -r mod; do
 ./guard.sh "lean-$mod" lean -M3500 -DwarningAsError=true -o "build/$mod.olean" "extracted/src/$mod.lean"
 ./guard.sh "checker-$mod" leanchecker "$mod"
done < extracted/module-order.txt

#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
L=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
python3 -I scripts/guard.py version "$L/lean" --version
for m in Basic Certificates Graph RealBridge; do
 python3 -I scripts/guard.py "build-$m" "$L/lean" -j1 -DwarningAsError=true -o "$m.olean" "$m.lean"
done
for m in Basic Certificates Graph RealBridge; do
 python3 -I scripts/guard.py "checker-$m" "$L/leanchecker" "$m"
done
python3 -I scripts/guard.py audit "$L/lean" -j1 -DwarningAsError=true Audit.lean
for m in WrongMPValue GroupAsMP Perturbed; do
 if python3 -I scripts/guard.py "negative-$m" "$L/lean" -j1 -DwarningAsError=true "../negative/$m.lean"; then exit 1; fi
done

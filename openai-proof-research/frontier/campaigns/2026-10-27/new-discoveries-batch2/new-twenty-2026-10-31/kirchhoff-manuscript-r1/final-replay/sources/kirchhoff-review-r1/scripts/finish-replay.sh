#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
L=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
for m in Basic Certificates Graph RealBridge; do
 python3 -I scripts/guard.py "checker-fixed-$m" "$L/leanchecker" "$m"
done
python3 -I scripts/guard.py audit "$L/lean" -j1 -DwarningAsError=true Audit.lean
python3 -I scripts/guard.py restatement "$L/lean" -j1 -DwarningAsError=true -o ReviewerRestatement.olean ReviewerRestatement.lean
for m in WrongMPValue GroupAsMP Perturbed; do
 if python3 -I scripts/guard.py "negative-$m" "$L/lean" -j1 -DwarningAsError=true "../negative/$m.lean"; then exit 1; fi
done

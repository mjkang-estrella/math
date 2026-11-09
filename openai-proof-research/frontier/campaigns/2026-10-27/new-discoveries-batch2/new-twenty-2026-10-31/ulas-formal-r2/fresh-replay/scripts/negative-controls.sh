#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
for test in endpoint functional; do
  name="negative-$test-$(date +%s%N)"
  if bash "$L/scripts/run.sh" "$name" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 -DwarningAsError=true "$L/scripts/negative-$test.lean"; then
    echo "ERROR: negative control unexpectedly passed"; exit 1
  fi
  grep -q 'Type mismatch' "$L/logs/$name.log"
  echo "$test: expected type mismatch confirmed"
done

#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
for f in negative-weight negative-unconditional; do
  if bash "$L/scripts/run.sh" "$f-$(date +%s%N)" lean -j1 -M3500 -DwarningAsError=true "$L/scripts/$f.lean"; then
    echo "Unexpected negative-control success: $f"; exit 1
  fi
done
echo 'Both negative controls rejected as required.'

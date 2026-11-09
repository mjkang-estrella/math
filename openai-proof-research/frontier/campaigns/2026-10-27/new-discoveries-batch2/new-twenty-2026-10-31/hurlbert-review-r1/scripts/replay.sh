#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
ROOT=$PWD
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin
export LEAN_PATH="$ROOT/replay"
for p in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*; do LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
cd replay
"$ROOT/scripts/capped.sh" lean -j1 -M3500 -DwarningAsError=true -o Hurlbert.olean Hurlbert.lean > "$ROOT/logs/build.log" 2>&1
"$ROOT/scripts/capped.sh" lean -j1 -M3500 -DwarningAsError=true Inventory.lean > "$ROOT/logs/inventory.log" 2>&1
"$ROOT/scripts/capped.sh" lean -j1 -M3500 -DwarningAsError=true AllAxioms.lean > "$ROOT/logs/axioms.log" 2>&1
"$ROOT/scripts/capped.sh" leanchecker Hurlbert > "$ROOT/logs/leanchecker.log" 2>&1

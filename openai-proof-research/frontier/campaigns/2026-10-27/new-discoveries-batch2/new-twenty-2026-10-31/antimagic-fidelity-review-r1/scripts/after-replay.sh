#!/bin/bash
set -eu
L=$(cd "$(dirname "$0")/.." && pwd)
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$L/build"; for p in "$P"/*; do if [ -d "$p/.lake/build/lib/lean" ]; then export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; fi; done
cd "$L"
"$L/scripts/capped.sh" spotcheck python3 -I "$L/scripts/spotcheck.py"
"$L/scripts/capped.sh" inspect python3 -I "$L/scripts/inspect.py"
"$L/scripts/capped.sh" independent-audit lean -j1 -M3500 -DwarningAsError=true -o "$L/build/ReviewAudit.olean" ReviewAudit.lean
"$L/scripts/capped.sh" independent-check leanchecker ReviewAudit
"$L/scripts/capped.sh" toolchain lean -M3500 --version

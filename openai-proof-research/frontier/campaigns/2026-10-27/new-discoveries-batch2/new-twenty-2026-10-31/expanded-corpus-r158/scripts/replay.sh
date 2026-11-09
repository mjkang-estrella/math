#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
R="${1:-$L/replay-final-audited}"
export PATH="$L/bin:/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH"
test ! -e "$R"
mkdir -p "$R/logs"
cp "${2:-$L/lean}/"*.lean "$R/"
cd "$R"
M=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$R"
for p in "$M"/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$p"; done
for mod in Definitions Witness Audit; do
 "$L/scripts/lean.sh" -o "$mod.olean" "$mod.lean" > "$R/logs/$mod.strict.log" 2>&1
 "$L/scripts/cap.sh" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker "$mod" > "$R/logs/$mod.checker.log" 2>&1
done

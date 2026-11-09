#!/bin/bash
set -eu
R=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/orientdom-review-r1
export PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:$PATH
export LEAN_PATH="$R/replay"
for p in /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/*/.lake/build/lib/lean; do export LEAN_PATH="$LEAN_PATH:$p"; done
cd "$R/replay"
case "$1" in
compile) exec lean -M3500 -j2 -DwarningAsError=true -o Interpolation.olean Interpolation.lean;;
check) exec leanchecker Interpolation;;
audit) exec lean -M3500 -j2 -DwarningAsError=true Audit.lean;;
esac

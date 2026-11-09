#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")/build"
T=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP="$PWD"; for d in "$P"/*/; do LP="$LP:${d}.lake/build/lib/lean"; done
run() { /usr/bin/time -v systemd-run --user --scope -q -p MemoryMax=12G -p CPUQuota=200% env -i HOME=/home/mj-kang PATH="$T:/usr/bin:/bin" LEAN_PATH="$LP" taskset -c 0,1 timeout -k 10 600 "$@"; }
run "$T/lean" -DwarningAsError=true -j2 -o ConferenceMDS324342.olean ConferenceMDS324342.lean > ../main.log 2> ../main.time
run "$T/lean" -DwarningAsError=true -j2 -o Controls.olean Controls.lean > ../controls.log 2> ../controls.time
run "$T/lean" -DwarningAsError=true -j2 IndependentAudit.lean > ../audit.log 2> ../audit.time
run "$T/leanchecker" ConferenceMDS324342 > ../checker.log 2> ../checker.time
printf 'PASS\n' > ../status.txt

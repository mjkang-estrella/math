#!/bin/bash
# Reviewer's strict sequential build: one module at a time, lean -j1 -DwarningAsError=true, each under cap.sh
# (systemd scope MemoryMax=6G + RSS watchdog 6 GiB private, CPU 120 s, wall 140 s, 2 CPUs, MALLOC_ARENA_MAX=2).
set -u
R=$(cd "$(dirname "$0")/.." && pwd); B=$R/lean-build
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP=""; for d in aesop batteries importGraph LeanSearchClient mathlib plausible proofwidgets Qq; do LP="$LP:$P/$d/.lake/build/lib/lean"; done
export LEAN_PATH="${LP#:}:$B/build"
unset LEAN_SRC_PATH LAKE LAKE_HOME ELAN_TOOLCHAIN
cd "${SRCDIR:-$B/src}"   # so PermOrder's #eval file write lands inside the review directory
for M in "$@"; do
  "$R/scripts/cap.sh" "$B/logs/$M.watch.json" env -i HOME=/nonexistent PATH=/usr/bin:/bin LEAN_PATH="$LEAN_PATH" MALLOC_ARENA_MAX=2 \
     "$LEAN" -j1 -DwarningAsError=true -o "$B/build/$M.olean" "$M.lean" > "$B/logs/$M.stdout" 2> "$B/logs/$M.stderr"
  rc=$?; echo "$M rc=$rc $(cat $B/logs/$M.watch.json | tr -d '\n ' | grep -o '"wall_s":[^,]*,"cpu_s":[^,]*,"peak_private_rss_MiB":[^,]*,"peak_total_rss_MiB":[^,]*')"
  [ $rc -ne 0 ] && { echo "STOP at $M"; exit $rc; }
done

#!/bin/bash
# leanchecker per module (sequential, capped). usage: check.sh [--fresh] MOD...
set -u
R=$(cd "$(dirname "$0")/.." && pwd); B=$R/lean-build
LC=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/leanchecker
P=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
LP=""; for d in aesop batteries importGraph LeanSearchClient mathlib plausible proofwidgets Qq; do LP="$LP:$P/$d/.lake/build/lib/lean"; done
LEAN_PATH="${LP#:}:$B/build"; FR=""; TAG=checker
if [ "$1" = "--fresh" ]; then FR="--fresh"; TAG=checker-fresh; shift; fi
cd "$B/src"
for M in "$@"; do
  "$R/scripts/cap.sh" "$B/logs/$M.$TAG.watch.json" env -i HOME=/nonexistent PATH=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin:/usr/bin:/bin LEAN_PATH="$LEAN_PATH" MALLOC_ARENA_MAX=2 \
     "$LC" $FR "$M" > "$B/logs/$M.$TAG.stdout" 2> "$B/logs/$M.$TAG.stderr"
  rc=$?; echo "$M $TAG rc=$rc $(tr -d '\n ' < $B/logs/$M.$TAG.watch.json | grep -o '"wall_s":[^,]*,"cpu_s":[^,]*,"peak_private_rss_MiB":[^,]*')"
done

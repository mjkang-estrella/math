#!/bin/sh
# Portable strict replay for the CommonBasis332371 endpoint (DRAFT dossier,
# lane common-basis-manuscript-pi-r2). No .olean files are shipped: this script
# rebuilds every module from src/ against user-supplied pinned dependencies.
#
# Required environment:
#   LEAN_BIN       directory containing the pinned lean and leanchecker binaries
#                  (the frozen lane used Lean 4.34.1)
#   LEAN_PACKAGES  directory of pinned dependency package checkouts with prebuilt
#   (optional)     .lake/build trees, e.g. .../formal/.lake/packages (mathlib
#                  d13f23b723b8a846827a245b89c10fc7d3f11612 in the frozen lane)
#
# Usage: sh replay.sh BUILD_DIR
#   BUILD_DIR is a fresh empty directory for generated .olean files and logs.
#
# Resource discipline (mirrors the frozen lane): at most 2 CPUs, CPU time 120 s,
# wall 140 s per process; set MALLOC_ARENA_MAX=2. Adjust taskset/ulimit to your
# host; the checks below do not require more.
set -eu

: "${LEAN_BIN:?Set LEAN_BIN to the pinned Lean bin directory}"
BUILD="${1:?Usage: sh replay.sh BUILD_DIR}"
mkdir -p "$BUILD"
BUILD="$(cd "$BUILD" && pwd)"

export MALLOC_ARENA_MAX=2
PATH="$LEAN_BIN:$PATH"
export PATH

PKG_PATH=""
if [ -n "${LEAN_PACKAGES:-}" ]; then
  PKG_PATH="$(find "$LEAN_PACKAGES" -path '*/.lake/build/lib/lean' -type d 2>/dev/null | paste -sd:)"
fi
export LEAN_PATH="$BUILD${PKG_PATH:+:$PKG_PATH}"

ORDER="Bases Cases0 Cases1 Cases2 Cases3 Cases4 Cases5 Cases6 Cases7 Endpoint Final Audit"

for M in $ORDER; do
  echo "=== lean $M"
  lean -j1 -M3500 -DwarningAsError=true -o "$BUILD/$M.olean" "src/$M.lean"
  echo "=== leanchecker $M"
  ( cd "$BUILD" && leanchecker "$M" )
done
echo "REPLAY COMPLETE: 12 modules compiled and kernel-checked"

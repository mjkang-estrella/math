#!/bin/bash
set -eu
LANE=$(cd "$(dirname "$0")/.." && pwd)
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export LEAN_PATH="$LANE/formal"
for p in "$PKG"/*; do export LEAN_PATH="$LEAN_PATH:$p/.lake/build/lib/lean"; done
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp/cache" MALLOC_ARENA_MAX=2
ulimit -t 120
ulimit -c 0
CPU=$(awk '/Cpus_allowed_list/ {split($2,a,"[-,]"); print a[1]}' /proc/self/status)
cd "$LANE/formal"
exec timeout 140s taskset -c "$CPU" /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -j1 -M3500 -o Partial.olean Partial.lean

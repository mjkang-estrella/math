#!/usr/bin/env bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
export TMPDIR="$LANE/tmp" XDG_CACHE_HOME="$LANE/tmp/cache" MALLOC_ARENA_MAX=2
export LEAN_PATH="$LANE/build"
PKG=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
for dir in "$PKG"/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$dir"; done
name="$1"; shift
[[ ! -e "$LANE/logs/$name.log" ]]
(ulimit -t 120; exec taskset -c 0,1 timeout 140 /usr/bin/time -v python3 -I "$LANE/scripts/bounded.py" "$@") >"$LANE/logs/$name.log" 2>"$LANE/logs/$name.stderr"

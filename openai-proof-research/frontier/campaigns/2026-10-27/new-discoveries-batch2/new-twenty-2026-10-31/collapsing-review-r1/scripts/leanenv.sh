#!/bin/bash
# usage: leanenv.sh WORKDIR cmd...  -- sets LEAN_PATH to WORKDIR + read-only mathlib cache libs
B=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
W=$1; shift
LP=$W
for d in $PK/*/.lake/build/lib/lean; do LP=$LP:$d; done
cd "$W" && env -i PATH=$B:/usr/bin:/bin HOME=$HOME LEAN_PATH=$LP LEAN_NUM_THREADS=1 MALLOC_ARENA_MAX=2 "$@"

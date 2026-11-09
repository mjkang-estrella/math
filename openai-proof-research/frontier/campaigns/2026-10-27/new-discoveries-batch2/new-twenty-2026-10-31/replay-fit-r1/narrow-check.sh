#!/bin/bash
set -eu
L=$(cd -- "$(dirname -- "$0")" && pwd)
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
id=$1
if [ "$id" = 330264 ]; then m=SpectralWitness; else m=ConferenceMDS324342; fi
cd "$L/narrow-$id"
export PATH="$BIN:/usr/bin:/bin" LEAN_PATH="$PWD:$L/build-$id"
for d in "$PK"/*; do LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; done
export LEAN_PATH
"$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/$id-narrow2.build.log" 2>&1

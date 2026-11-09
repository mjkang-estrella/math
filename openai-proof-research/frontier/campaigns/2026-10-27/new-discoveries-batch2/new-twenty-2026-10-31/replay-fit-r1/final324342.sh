#!/bin/bash
set -eu
L=$(cd -- "$(dirname -- "$0")" && pwd)
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
cd "$L/${1:-fresh-324342}"
TAG=${2:-final324342}
export PATH="$BIN:/usr/bin:/bin" LEAN_PATH="$PWD"
for d in "$PK"/*; do LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; done
export LEAN_PATH
for m in ConferenceMDS324342 Controls Audit MetadataAudit; do
 if [ -f "$L/logs/${TAG}-$m.ok" ] && [ -f "$m.olean" ]; then continue; fi
 echo "Build/check $m"
 "$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/${TAG}-$m.build.log" 2>&1
 "$L/run" "$BIN/leanchecker" "$m" > "$L/logs/${TAG}-$m.check.log" 2>&1
 touch "$L/logs/${TAG}-$m.ok"
done
cp metadata.tsv "$L/logs/${TAG}-metadata.tsv"

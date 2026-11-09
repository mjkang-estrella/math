#!/bin/bash
set -eu
L=$(cd -- "$(dirname -- "$0")" && pwd)
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export PATH="$BIN:/usr/bin:/bin" TMPDIR="$L/tmp" TMP="$L/tmp" TEMP="$L/tmp" XDG_CACHE_HOME="$L/cache" MALLOC_ARENA_MAX=2
id=$1
mkdir -p "$L/build-$id"
cp "$L/original-$id/"*.lean "$L/build-$id/"
cd "$L/build-$id"
export LEAN_PATH="$PWD"
for d in "$PK"/*; do LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; done
export LEAN_PATH
if [ "$id" = 330264 ]; then
 modules='GroupSemantics NormalForm TraceAction AutomatonSemantics WordCounting MachineInvariant SpectralDefinitions ConcreteMachine SpectralWitness Endpoint'
else
 modules='ConferenceMDS324342 Audit Controls'
fi
for m in $modules; do
 if [ -f "$L/logs/$id-$m.ok" ] && [ -f "$m.olean" ]; then continue; fi
 echo "Building $id $m"
 "$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/$id-$m.build.log" 2>&1 || { echo "Stopped $m build"; exit 1; }
 "$L/run" "$BIN/leanchecker" "$m" > "$L/logs/$id-$m.check.log" 2>&1 || { echo "Stopped $m checker"; exit 1; }
 touch "$L/logs/$id-$m.ok"
done

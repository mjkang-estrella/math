#!/bin/bash
set -u
L=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/held-reopen-r1
BIN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
PK=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
export PATH="$BIN:/usr/bin:/bin"
export LEAN_PATH="$L/replay-$1"
for d in "$PK"/*; do export LEAN_PATH="$LEAN_PATH:$d/.lake/build/lib/lean"; done
cd "$L/replay-$1"
if [ "$1" = 330264 ]; then
 modules="GroupSemantics NormalForm TraceAction AutomatonSemantics WordCounting MachineInvariant SpectralDefinitions ConcreteMachine SpectralWitness Endpoint"
else
 modules="ConferenceMDS324342"
fi
: > "$L/logs/replay-$1.status"
for m in $modules; do
 "$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "$L/logs/$1-$m.build.log" 2>&1
 r=$?
 echo "build $m $r" >> "$L/logs/replay-$1.status"
 [ "$r" = 0 ] || exit "$r"
 "$L/run" "$BIN/leanchecker" "$m" > "$L/logs/$1-$m.check.log" 2>&1
 r=$?
 echo "checker $m $r" >> "$L/logs/replay-$1.status"
 [ "$r" = 0 ] || exit "$r"
done
if [ "$1" = 330264 ]; then
 echo 'import Endpoint' > ReopenAudit.lean
 echo '#print MathDB330264.Conjecture' >> ReopenAudit.lean
 echo '#print axioms MathDB330264.conjecture_false' >> ReopenAudit.lean
else
 echo 'import ConferenceMDS324342' > ReopenAudit.lean
 echo '#print ConferenceMDS.Conjecture5' >> ReopenAudit.lean
 echo '#print axioms ConferenceMDS.conjecture5_false' >> ReopenAudit.lean
fi
"$L/run" "$BIN/lean" -j2 -M3500 -DwarningAsError=true ReopenAudit.lean > "$L/logs/$1-endpoint-audit.log" 2>&1
echo "audit $?" >> "$L/logs/replay-$1.status"

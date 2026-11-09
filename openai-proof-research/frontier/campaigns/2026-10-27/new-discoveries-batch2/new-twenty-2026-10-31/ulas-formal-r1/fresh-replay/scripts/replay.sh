#!/usr/bin/env bash
set -eu
LANE="$(cd "$(dirname "$0")/.." && pwd)"
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
mkdir -p "$LANE/logs" "$LANE/build" "$LANE/tmp"
cd "$LANE/src"
for m in UlasSeries UlasFinal UlasChecks UlasAudit; do
  if [[ -e "$LANE/build/$m.olean" && "$LANE/build/$m.olean" -nt "$m.lean" ]]; then continue; fi
  name="replay-$m-$(date +%s%N)"
  export ULAS_AUDIT_OUT="$LANE/logs/declarations-0.jsonl" ULAS_AUDIT_SHARD=0
  bash "$LANE/scripts/run.sh" "$name" "$LEAN/lean" -j1 -M3500 -DwarningAsError=true -o "$LANE/build/$m.olean" "$m.lean"
done
for shard in 1 2 3 4 5 6 7; do
  export ULAS_AUDIT_OUT="$LANE/logs/declarations-$shard.jsonl" ULAS_AUDIT_SHARD="$shard"
  bash "$LANE/scripts/run.sh" "audit-shard-$shard-$(date +%s%N)" "$LEAN/lean" -j1 -M3500 -DwarningAsError=true UlasAudit.lean
done
for m in UlasSeries UlasFinal UlasChecks UlasAudit; do
  bash "$LANE/scripts/run.sh" "checker-$m-$(date +%s%N)" "$LEAN/leanchecker" "$m"
done
bash "$LANE/scripts/run.sh" "audit-analysis-$(date +%s%N)" python3 -I "$LANE/scripts/analyze_audit.py" "$LANE/logs/declarations-*.jsonl" "$LANE/logs/audit-summary.json"
bash "$LANE/scripts/run.sh" "regression-$(date +%s%N)" python3 -I "$LANE/scripts/regression.py"

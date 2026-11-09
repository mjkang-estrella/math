#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
LEAN=/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin
mkdir -p "$L/logs" "$L/tmp" "$L/build"
cd "$L/src"
for m in UlasSeries UlasFinal UlasChecks UlasOperator UlasParity UlasLow UlasFinal2 UlasAudit UlasAudit2; do
  if [[ -e "$L/build/$m.olean" && "$L/build/$m.olean" -nt "$m.lean" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/frozen-declarations.jsonl" ULAS_AUDIT_SHARD=0
  if [[ "$m" == UlasAudit2 ]]; then export ULAS_AUDIT_OUT="$L/logs/declarations-0.jsonl"; fi
  bash "$L/scripts/build-one.sh" "$m"
done
for shard in 1 2 3 4 5 6 7; do
  if [[ -e "$L/logs/audit-$shard.done" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/declarations-$shard.jsonl" ULAS_AUDIT_SHARD="$shard"
  bash "$L/scripts/run.sh" "audit-$shard-$(date +%s%N)" "$LEAN/lean" -j1 -M3500 -DwarningAsError=true UlasAudit2.lean
  touch "$L/logs/audit-$shard.done"
done
for m in UlasSeries UlasFinal UlasChecks UlasOperator UlasParity UlasLow UlasFinal2 UlasAudit UlasAudit2; do
  if [[ -e "$L/logs/checker-$m.done" ]]; then continue; fi
  bash "$L/scripts/run.sh" "checker-$m-$(date +%s%N)" "$LEAN/leanchecker" "$m"
  touch "$L/logs/checker-$m.done"
done
bash "$L/scripts/run.sh" "audit-analysis-$(date +%s%N)" python3 -I "$L/scripts/analyze_audit2.py" "$L/logs/declarations-*.jsonl" "$L/logs/audit-summary.json"
bash "$L/scripts/run.sh" "regression-$(date +%s%N)" python3 -I "$L/scripts/regression.py"
bash "$L/scripts/run.sh" "regression2-$(date +%s%N)" python3 -I "$L/scripts/regression2.py"
bash "$L/scripts/negative-controls.sh"

#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$L/build" "$L/logs" "$L/tmp"
cd "$L/src"
modules=(UlasSeries UlasFinal UlasChecks UlasOperator UlasParity UlasLow UlasFinal2 UlasWeight UlasFinal3 UlasAudit UlasAudit2 UlasAudit3 UlasBridge UlasBinomial UlasReadout UlasPositive UlasExactReadout UlasInvariant UlasInitialization UlasFinal4 UlasAudit4 UlasEven5Pell UlasEven5Coefficients UlasEven5Kummer UlasEven5Invariant UlasEven5Final UlasEven5Audit)
for m in "${modules[@]}"; do
  if [[ -f "$L/build/$m.olean" && "$L/build/$m.olean" -nt "$m.lean" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/frozen-$m.jsonl" ULAS_AUDIT_SHARD=0
  if [[ "$m" == UlasEven5Audit ]]; then export ULAS_AUDIT_OUT="$L/logs/declarations-0.jsonl"; fi
  bash "$L/scripts/run.sh" "build-$m-$(date +%s%N)" lean -j1 -M3500 -DwarningAsError=true -o "$L/build/$m.olean" "$m.lean"
  echo "BUILT $m"
done
for shard in 1 2 3 4 5 6 7; do
  if [[ -e "$L/logs/audit-$shard.done" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/declarations-$shard.jsonl" ULAS_AUDIT_SHARD="$shard"
  bash "$L/scripts/run.sh" "audit-$shard-$(date +%s%N)" lean -j1 -M3500 -DwarningAsError=true UlasEven5Audit.lean
  touch "$L/logs/audit-$shard.done"
  echo "AUDITED $shard"
done
for m in "${modules[@]}"; do
  if [[ -e "$L/logs/checker-$m.done" ]]; then continue; fi
  bash "$L/scripts/run.sh" "checker-$m-$(date +%s%N)" leanchecker "$m"
  touch "$L/logs/checker-$m.done"
  echo "CHECKED $m"
done
bash "$L/scripts/run.sh" "audit-analysis-$(date +%s%N)" python3 -I "$L/scripts/analyze_even5.py" "$L/logs/declarations-*.jsonl" "$L/logs/audit-summary.json"
bash "$L/scripts/run.sh" "regression-$(date +%s%N)" python3 -I "$L/scripts/regression5a.py"
bash "$L/scripts/negative5a.sh"
echo 'REPLAY COMPLETE'

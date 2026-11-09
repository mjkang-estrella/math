#!/bin/bash
set -eu
L="$(cd "$(dirname "$0")/.." && pwd)"
mkdir -p "$L/logs" "$L/tmp" "$L/build"
cd "$L/src"
modules=(UlasSeries UlasFinal UlasChecks UlasOperator UlasParity UlasLow UlasFinal2 UlasWeight UlasFinal3 UlasAudit UlasAudit2 UlasAudit3 UlasBridge UlasBinomial UlasReadout UlasPositive UlasExactReadout UlasInvariant UlasInitialization UlasFinal4 UlasAudit4 UlasOdd5Initialization UlasOdd5HalfAngle UlasOdd5Transfer UlasOdd5Crude UlasOdd5Factorization UlasOdd5Representative UlasOdd5One UlasOdd5Residues UlasOdd5Coefficients UlasOdd5PowerCoefficients UlasOdd5LowIdentification UlasOdd5Bounds UlasOdd5Equality UlasOdd5Final UlasOdd5Audit)
for m in "${modules[@]}"; do
  if [[ -f "$L/build/$m.olean" && "$L/build/$m.olean" -nt "$m.lean" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/frozen-$m.jsonl" ULAS_AUDIT_SHARD=0
  if [[ "$m" == UlasOdd5Audit ]]; then export ULAS_AUDIT_OUT="$L/logs/declarations-0.jsonl"; fi
  bash "$L/scripts/run.sh" "build-$m-$(date +%s%N)" lean -j1 -M3500 -DwarningAsError=true -o "$L/build/$m.olean" "$m.lean"
done
for shard in 1 2 3 4 5 6 7; do
  if [[ -e "$L/logs/audit-$shard.done" ]]; then continue; fi
  export ULAS_AUDIT_OUT="$L/logs/declarations-$shard.jsonl" ULAS_AUDIT_SHARD="$shard"
  bash "$L/scripts/run.sh" "audit-$shard-$(date +%s%N)" lean -j1 -M3500 -DwarningAsError=true UlasOdd5Audit.lean
  touch "$L/logs/audit-$shard.done"
done
for m in "${modules[@]}"; do
  if [[ -e "$L/logs/checker-$m.done" ]]; then continue; fi
  bash "$L/scripts/run.sh" "checker-$m-$(date +%s%N)" leanchecker "$m"
  touch "$L/logs/checker-$m.done"
done
bash "$L/scripts/run.sh" "audit-analysis-$(date +%s%N)" python3 -I "$L/scripts/analyze_audit5.py" "$L/logs/declarations-*.jsonl" "$L/logs/audit-summary.json"
bash "$L/scripts/run.sh" "regression-$(date +%s%N)" python3 -I "$L/scripts/regression.py"
bash "$L/scripts/run.sh" "regression2-$(date +%s%N)" python3 -I "$L/scripts/regression2.py"
bash "$L/scripts/run.sh" "regression3-$(date +%s%N)" python3 -I "$L/scripts/regression3.py"
bash "$L/scripts/negative-controls4.sh"

bash "$L/scripts/run.sh" "regression4-$(date +%s%N)" python3 -I "$L/scripts/regression4.py"
bash "$L/scripts/run.sh" "regression5-$(date +%s%N)" python3 -I "$L/scripts/regression5.py"
bash "$L/scripts/negative-controls5.sh"

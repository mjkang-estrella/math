#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
MODULES=(StackSortBasic StackSortMap StackSortSplit StackSortEquivariance StackSortAnalysis StackSortMaximum StackSortCertificate StackSortControls StackSortSmall StackSortFinal)
dirty=0
for m in "${MODULES[@]}"; do
  if [ "$dirty" = 1 ] || [ ! -f "$m.olean" ] || [ "$m.lean" -nt "$m.olean" ]; then
    dirty=1
    scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean"
  fi
done
export STACKSORT_AUDIT_OUT="$PWD/audit.jsonl"
scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o StackSortAudit.olean StackSortAudit.lean
scripts/run.sh python3 -I scripts/check_audit.py audit.jsonl

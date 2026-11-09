#!/bin/bash
set -eu
mkdir -p build tmp cache logs
DIRTY=0
LATEST=""
compile() {
 local m="$1" src="$2" log="logs/build-$1.txt"
 if [ "$DIRTY" = 1 ] || [ ! -f "build/$m.olean" ] || [ "$src" -nt "build/$m.olean" ] || [ ! -s "$log" ] || { [ -n "$LATEST" ] && [ "$LATEST" -nt "build/$m.olean" ]; }; then
  scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o "build/$m.olean" "$src" > "$log"
  DIRTY=1
 fi
 if [ -z "$LATEST" ] || [ "build/$m.olean" -nt "$LATEST" ]; then LATEST="build/$m.olean"; fi
}
for m in StackSortBasic StackSortMap StackSortSplit StackSortEquivariance StackSortAnalysis StackSortMaximum StackSortCertificate StackSortControls StackSortSmall StackSortFinal; do compile "$m" "frozen/$m.lean"; done
STACKSORT_AUDIT_OUT="$PWD/frozen-audit.jsonl" scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o build/StackSortAudit.olean frozen/StackSortAudit.lean > logs/build-StackSortAudit.txt
for m in StackSortSeeds2Words StackSortSeeds2Tuples StackSortSeeds2Maximum StackSortSeeds2Recursion StackSortSeeds2Data; do compile "$m" "$m.lean"; done
for n in $(seq -w 1 20); do m=StackSortSeeds2Row$n; compile "$m" "$m.lean"; done
for m in StackSortSeeds2Checked StackSortSeeds2Domain StackSortSeeds2Final StackSortSeeds2Controls; do compile "$m" "$m.lean"; done
STACKSORT_AUDIT_OUT="$PWD/audit.jsonl" scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o build/StackSortSeeds2Audit.olean StackSortSeeds2Audit.lean > logs/build-StackSortSeeds2Audit.txt
scripts/run.sh python3 -I scripts/check_audit.py audit.jsonl > logs/check-audit.txt
for src in frozen/*.lean StackSortSeeds2*.lean; do
 m=$(basename "$src" .lean)
 (cd build; ../scripts/run.sh leanchecker "$m") > "logs/checker-$m.txt"
done

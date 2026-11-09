#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
mkdir -p logs tmp cache
export STACKSORT_AUDIT_OUT="$PWD/audit.jsonl"
while read -r m; do
 if [ "$m" = StackSortAudit ]; then export STACKSORT_AUDIT_OUT="$PWD/frozen-audit.jsonl"; fi
 if [ "$m" = StackSortInj2Audit ]; then export STACKSORT_AUDIT_OUT="$PWD/audit.jsonl"; fi
 ./scripts/run.sh lean -j1 -M3500 -DwarningAsError=true -o "$m.olean" "$m.lean" > "logs/replay-build-$m.log"
done < scripts/order.txt
./scripts/run.sh python3 -I scripts/check_audit.py audit.jsonl > logs/check-audit.log
while read -r m; do
 ./scripts/run.sh leanchecker "$m" > "logs/checker-$m.log"
done < scripts/order.txt

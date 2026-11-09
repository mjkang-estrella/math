#!/bin/bash
set -eu
bash scripts/build.sh
for m in $(cat scripts/order.txt); do
 (cd src; ../scripts/run.sh leanchecker "$m") > "logs/checker-$m.log"
done
scripts/run.sh python3 -I scripts/check_audit.py logs/StackSortAudit3-audit.jsonl > logs/audit-report.log

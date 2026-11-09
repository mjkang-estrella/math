#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
mkdir -p logs tmp cache
bash scripts/build.sh
cd src
for m in $(cat ../scripts/order.txt); do
 ../scripts/run.sh leanchecker "$m" > "../logs/checker-$m.log"
done
../scripts/run.sh python3 -I ../scripts/check_audit4.py ../logs/StackSortAudit4-audit.jsonl > ../logs/audit-report4.log

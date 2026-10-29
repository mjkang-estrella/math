#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python exact.py > logs/exact.log 2> logs/exact-guard.json
python capped_run.py python scan.py > logs/scan.log 2> logs/scan-guard.json
python capped_run.py python audit.py > logs/audit.log 2> logs/audit-guard.json

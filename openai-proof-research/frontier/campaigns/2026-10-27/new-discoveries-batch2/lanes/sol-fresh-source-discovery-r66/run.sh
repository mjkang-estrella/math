#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python screen.py > logs/context.log 2> logs/context-guard.json
python capped_run.py python scan.py > logs/scan.log 2> logs/scan-guard.json
python capped_run.py python scan.py --exact > logs/exact-scan.log 2> logs/exact-scan-guard.json
python capped_run.py python routes.py > logs/routes.log 2> logs/routes-guard.json
python capped_run.py python mixture.py > logs/mixture.log 2> logs/mixture-guard.json
python capped_run.py python extend.py > logs/extend.log 2> logs/extend-guard.json
python capped_run.py python audit.py --exact > logs/audit.log 2> logs/audit-guard.json
python capped_run.py python obstructions.py > logs/obstructions.log 2> logs/obstructions-guard.json

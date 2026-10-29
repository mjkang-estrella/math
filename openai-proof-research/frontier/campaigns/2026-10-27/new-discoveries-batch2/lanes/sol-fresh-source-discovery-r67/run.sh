#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p logs
for script in routes independent abel kernel; do
  python capped_run.py python "$script.py" >"logs/$script.log" 2>"logs/$script-guard.json"
done
python capped_run.py python finalize.py >logs/finalize.log 2>logs/finalize-guard.json

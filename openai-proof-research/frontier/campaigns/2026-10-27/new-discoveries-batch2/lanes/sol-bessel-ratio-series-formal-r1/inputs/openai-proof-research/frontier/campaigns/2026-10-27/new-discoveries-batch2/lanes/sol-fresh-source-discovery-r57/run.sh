#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 capped_run.py python3 check.py > check-run.log 2>check-guard.json
cat check-run.log check-guard.json

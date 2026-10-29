#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python check.py > check.log 2> check-guard.json

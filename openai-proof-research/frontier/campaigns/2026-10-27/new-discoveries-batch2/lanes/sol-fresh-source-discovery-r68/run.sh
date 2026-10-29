#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python check.py 2 250 > check-2-250.log 2> check-2-250-guard.json
python capped_run.py python check.py 251 1000 > check-251-1000.log 2> check-251-1000-guard.json
python capped_run.py python routes.py > routes.log 2> routes-guard.json

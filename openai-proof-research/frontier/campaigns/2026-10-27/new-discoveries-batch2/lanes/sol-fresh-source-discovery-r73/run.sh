#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python exact.py > logs/exact.txt 2> logs/exact-guard.json
python capped_run.py python routes.py > logs/routes.txt 2> logs/routes-guard.json

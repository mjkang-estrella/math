#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 capped_run.py python3 check.py > check.stdout.json 2> check.guard.json
python3 capped_run.py python3 kernel.py > kernel.stdout.json 2> kernel.guard.json

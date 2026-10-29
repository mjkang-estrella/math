#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python check.py > checks.json.log 2> checks.guard.json
python capped_run.py python routes.py > routes.json 2> routes.guard.json
python capped_run.py python denumerant.py > denumerant.json 2> denumerant.guard.json

#!/bin/bash
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py > check.log 2> check.guard.json
python helper_guard.py python analyze.py > analyze.log 2> analyze.guard.json
python helper_guard.py python route.py > route.log 2> route.guard.json
python helper_guard.py python shift.py > shift.log 2> shift.guard.json
python helper_guard.py python validate.py > validate.log 2> validate.guard.json

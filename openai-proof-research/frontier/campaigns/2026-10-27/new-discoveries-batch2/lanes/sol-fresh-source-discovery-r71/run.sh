#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python exact.py > logs/exact.log 2> logs/exact-guard.json
python capped_run.py python route.py > logs/route.log 2> logs/route-guard.json
python capped_run.py python identity.py > logs/identity.log 2> logs/identity-guard.json

#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python exact_check.py > replay-exact.log 2> replay-exact-guard.json
python capped_run.py python attempt.py > replay-airy.log 2> replay-airy-guard.json

#!/bin/sh
set -eu
cd "$(dirname "$0")"
python capped_run.py python check.py > check.log 2> check-guard.json
python capped_run.py python certificate.py > certificate.log 2> certificate-guard.json
python capped_run.py python compact.py > compact.log 2> compact-guard.json

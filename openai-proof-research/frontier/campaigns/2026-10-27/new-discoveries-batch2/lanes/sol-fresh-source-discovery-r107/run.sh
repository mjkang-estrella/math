#!/bin/sh
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py > check.log 2> check.guard.json

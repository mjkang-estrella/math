#!/bin/sh
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py > replay.log 2> replay.guard.json
python helper_guard.py python verify.py

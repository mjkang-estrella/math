#!/bin/sh
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py > check-result.json 2>check-guard.json

#!/bin/sh
set -eu
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
python helper_guard.py python check.py
python helper_guard.py python route.py
python helper_guard.py python verify.py

#!/bin/sh
set -eu
cd "$(dirname "$0")"
python helper_guard.py python check.py
python helper_guard.py python invariant.py
python helper_guard.py python reduction.py

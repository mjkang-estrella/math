#!/usr/bin/env bash
set -eu
cd -- "$(dirname -- "$0")"
python helper_guard.py python check.py
python helper_guard.py python validate.py

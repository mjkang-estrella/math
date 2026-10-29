#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 capped_run.py python3 check.py
python3 capped_run.py python3 tuple_check.py

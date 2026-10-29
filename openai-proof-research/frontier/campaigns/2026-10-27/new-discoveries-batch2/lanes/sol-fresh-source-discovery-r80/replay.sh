#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python capped_run.py python check.py
python capped_run.py python route_checks.py
# One optional bounded larger recurrence check (~62 seconds in this run):
# python capped_run.py python check-large.py
# Network retrieval/audit are separate from the mathematical replay:
# python capped_run.py python fetch.py
# python capped_run.py python audit.py

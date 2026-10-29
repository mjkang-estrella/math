#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python helper_guard.py python check.py
python helper_guard.py python certificate.py

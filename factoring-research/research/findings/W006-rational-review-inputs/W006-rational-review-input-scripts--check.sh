#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
python_bin=python3
if [[ -x .venv/bin/python ]]; then python_bin=.venv/bin/python; fi
"$python_bin" -m unittest discover -s tests -v
"$python_bin" scripts/audit_source.py
./scripts/lake.sh build
./scripts/lake.sh env lean Audit.lean


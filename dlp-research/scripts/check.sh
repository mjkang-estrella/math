#!/usr/bin/env bash
set -euo pipefail
project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
# Honest-mistake screening, not a sandbox or a substitute for proof review.
python3 scripts/audit_source.py
scripts/lake.sh build
audit_output="$(scripts/lake.sh env lean Audit.lean)"
printf '%s\n' "$audit_output"
printf '%s\n' "$audit_output" | python3 scripts/audit_axioms.py
scripts/lake.sh exe research_demo

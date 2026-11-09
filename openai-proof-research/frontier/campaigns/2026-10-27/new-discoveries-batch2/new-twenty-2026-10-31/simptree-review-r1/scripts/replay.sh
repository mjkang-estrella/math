#!/bin/bash
set -eu
L=$(cd "$(dirname "$0")/.." && pwd)
cd "$L/.."
sha256sum -c "$L/evidence/inputs-before.sha256"
"$L/scripts/capped.sh" python3 -I "$L/scripts/check.py"
"$L/scripts/capped.sh" python3 -I "$L/scripts/summarize.py"
"$L/scripts/capped.sh" python3 -I "$L/scripts/context.py"
sha256sum -c "$L/evidence/inputs-before.sha256"
"$L/scripts/capped.sh" python3 -I "$L/scripts/validate.py"

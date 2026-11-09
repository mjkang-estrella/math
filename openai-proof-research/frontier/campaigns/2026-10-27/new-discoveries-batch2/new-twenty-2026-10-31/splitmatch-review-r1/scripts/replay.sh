#!/bin/bash
set -euo pipefail
L=$(cd "$(dirname "$0")/.." && pwd)
# Offline replay: source packet was safely extracted by prepare.py; do not execute packet scripts.
sha256sum -c "$L/inputs-before.sha256" > "$L/logs/replay-inputs.log"
"$L/scripts/cap.sh" python3 -I "$L/scripts/validate_inputs.py" > "$L/logs/replay-provenance.log" 2>&1
"$L/scripts/cap.sh" python3 -I "$L/scripts/mathcheck.py" > "$L/logs/replay-math.log" 2>&1
"$L/scripts/cap.sh" "$L/scripts/lean.sh" -o SplitMatching.olean SplitMatching.lean > "$L/logs/replay-lean.log" 2>&1
"$L/scripts/cap.sh" "$L/scripts/lean.sh" -o Audit.olean Audit.lean > "$L/logs/replay-audit.log" 2>&1
"$L/scripts/cap.sh" "$L/scripts/lean.sh" checker > "$L/logs/replay-checker.log" 2>&1
"$L/scripts/cap.sh" "$L/scripts/lean.sh" -o EndpointSpec.olean EndpointSpec.lean > "$L/logs/replay-spec.log" 2>&1
sha256sum -c "$L/inputs-before.sha256" > "$L/logs/replay-inputs-after.log"

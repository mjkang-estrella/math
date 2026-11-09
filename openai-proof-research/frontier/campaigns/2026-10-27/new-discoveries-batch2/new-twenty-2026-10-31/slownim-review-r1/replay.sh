#!/bin/bash
set -euo pipefail
lane=$(cd "$(dirname "$0")" && pwd)
cd /home/mj-kang/Documents/Dev/math
sha256sum -c "$lane/inputs.before.sha256" > "$lane/logs/hash-check-$(date -u +%Y%m%dT%H%M%S%N).log"
log=$(mktemp "$lane/logs/independent-replay-XXXXXXXX.json")
"$lane/scripts/run.sh" python3 -I "$lane/scripts/check.py" > "$log"
echo "$log"

#!/bin/bash
set -euo pipefail
lane="$(cd -- "$(dirname -- "$0")" && pwd)"
guard="$lane/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
python "$guard" python "$lane/check.py"
python "$guard" python "$lane/verify.py"

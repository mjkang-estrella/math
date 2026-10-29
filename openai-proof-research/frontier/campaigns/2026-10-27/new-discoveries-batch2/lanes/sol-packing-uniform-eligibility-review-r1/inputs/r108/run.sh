#!/usr/bin/env bash
set -euo pipefail
lane="$(cd -- "$(dirname -- "$0")" && pwd)"
guard="$lane/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py"
for script in check.py uniform.py verify.py; do
  python "$guard" python "$lane/$script"
done

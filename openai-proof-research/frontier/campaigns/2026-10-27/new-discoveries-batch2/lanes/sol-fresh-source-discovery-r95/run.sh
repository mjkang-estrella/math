#!/bin/bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
guard=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python check.py

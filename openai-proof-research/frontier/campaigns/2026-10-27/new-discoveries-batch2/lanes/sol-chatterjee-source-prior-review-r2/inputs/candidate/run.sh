#!/bin/bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
python ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python check.py

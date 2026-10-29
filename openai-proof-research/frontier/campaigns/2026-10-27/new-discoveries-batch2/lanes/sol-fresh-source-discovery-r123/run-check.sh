#!/bin/sh
set -eu
LANE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$GUARD" python "$LANE/checks.py"
python "$GUARD" python "$LANE/finish.py" verify

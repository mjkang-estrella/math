#!/bin/sh
set -eu
lane=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
guard=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python "$lane/checks.py"
python "$guard" python "$lane/verify_manifest.py"

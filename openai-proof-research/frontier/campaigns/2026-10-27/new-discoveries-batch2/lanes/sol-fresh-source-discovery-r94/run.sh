#!/bin/sh
set -eu
cd "$(dirname "$0")"
GUARD=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
for name in context analyze exact check; do
 python "$GUARD" python "$name.py" > "$name.log" 2> "$name.guard.jsonl"
done

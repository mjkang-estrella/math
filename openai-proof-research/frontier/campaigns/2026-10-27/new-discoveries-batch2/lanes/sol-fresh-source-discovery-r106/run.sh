#!/bin/bash
set -eu
cd /home/mj-kang/Documents/Dev/math
lane=openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r106
guard=openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python "$lane/check.py"

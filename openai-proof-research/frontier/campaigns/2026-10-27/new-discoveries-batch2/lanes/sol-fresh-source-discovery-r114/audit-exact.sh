#!/bin/bash
set -euo pipefail
out=/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r114
rg --hidden --pcre2 -n -o -i '.{0,100}(?:supertoken|super.token|mycielski|hameed|semi.transitiv|mortada|local girth|(?<![0-9])(?:2412[.]20558|366438|2603[.]25113|373855)(?![0-9])).{0,180}' /home/mj-kang/Documents/Dev/math/openai-proof-research \
 -g '*.md' -g '*.txt' -g '*.json' -g '*.jsonl' -g '*.py' -g '*.sh' -g '*.lean' -g '*.tex' -g '*.html' -g '*.raw' \
 -g '!**/.git/**' -g '!**/.lake/**' -g '!**/node_modules/**' -g '!**/.venv/**' \
 -g '!**/*inventory-content*' -g '!**/*required-content*' -g '!**/*semantic-hits*' -g '!**/*semantic-reads*' -g '!**/*screen-content*' -g '!**/*supplement-content*' -g '!**/*duplicate-corpus*' -g '!**/*join-corpus*' \
 -g '!**/sol-fresh-source-discovery-r114/**' > "$out/audit-exact-bounded.txt"

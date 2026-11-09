#!/bin/bash
D=$(cd "$(dirname "$0")/.." && pwd)
B=$(cd "$D/../.." && pwd)
rg --no-ignore -n --max-columns 1200 -f "$D/scripts/history-ids.txt" "$B" -g '*.md' -g '*results*.json' -g '*ledger*.json' -g '!**/expanded-corpus-r162/**' -g '!**/sources/**' -g '!**/raw/**' -g '!**/corpus/**'
rc=$?
if [ "$rc" -gt 1 ]; then exit "$rc"; fi
rg --no-ignore -n -F --max-columns 1200 -f "$D/scripts/history-titles.txt" "$B" -g '*.md' -g '*results*.json' -g '*ledger*.json' -g '!**/expanded-corpus-r162/**' -g '!**/sources/**' -g '!**/raw/**' -g '!**/corpus/**'
rc=$?
if [ "$rc" -gt 1 ]; then exit "$rc"; fi
exit 0

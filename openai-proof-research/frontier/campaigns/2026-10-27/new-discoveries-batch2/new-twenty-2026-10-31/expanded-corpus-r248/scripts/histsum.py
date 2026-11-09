"""Summarise history-matches.txt: per hit print file (relative) and a trimmed snippet (read-only)."""
import sys
p = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248/history-matches.txt'
pref = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/'
width = int(sys.argv[1]) if len(sys.argv) > 1 else 300
import re
for line in open(p).read().splitlines()[1:]:
    f, k, s = line.split('::', 2)
    if re.search(r'\d' + re.escape(k) + r'|' + re.escape(k) + r'\d', s):
        continue
    print(k, '|', f.replace(pref, ''), '|', s[:width])

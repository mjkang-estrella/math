"""Print sha and commit date of cached HEAD bodies (read-only)."""
import json
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248/sources/'
for n in ['pool-head', 'omega-head', 'openai-head']:
    o = json.load(open(D + n + '.body'))
    print(n, o['sha'], o['commit']['committer']['date'], o['commit']['message'][:100].replace('\n', ' '))

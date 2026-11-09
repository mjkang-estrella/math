"""Show registry-screen snippets for given keys (read-only)."""
import json, sys
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
r = json.load(open(D + '/outputs/registry-screen.json'))
for k in sys.argv[1:]:
    for label, v in r['hits'].get(k, {}).items():
        print('==', k, label, v['count'])
        for s in v['snippets']:
            print('   ', s)

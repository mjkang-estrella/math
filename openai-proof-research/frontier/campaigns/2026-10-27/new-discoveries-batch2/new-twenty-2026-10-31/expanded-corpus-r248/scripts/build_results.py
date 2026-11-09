"""Assemble results.json (20 ID-keyed entries) from extracted.json (exact provenance) and outputs/dispositions.json.
Refuses to overwrite results.json."""
import json, os
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
if os.path.exists(D + '/results.json'):
    raise SystemExit('exists')
ex = json.load(open(D + '/extracted.json'))
dis = json.load(open(D + '/outputs/dispositions.json'))
assert set(ex) == set(dis) and len(ex) == 20
src_files = sorted(os.listdir(D + '/sources'))
out = {}
for i in sorted(ex):
    e = ex[i]
    arx = e['source_url'].rsplit('/', 1)[1]
    out[i] = {
        'mathdb_id': int(i),
        'title': e['title'],
        'literal_statement': e['statement'],
        'source_url': e['source_url'],
        'provenance': e['provenance'],
        'source_receipts': [f for f in src_files if arx in f and f.endswith('.receipt.json')],
        'history_screen': 'history-matches.txt: no prior campaign disposition of this ID (hits are the ledger launch note, sibling IDs from the same sources in r163/r188/r215/r17, and numeric coincidences)',
        'registry_screen': 'outputs/registry-screen.json: Lean Pool 01db1d70, Omega cae7cdbe, OpenAI 4eaee875; no prior Lean proof or refutation of this statement; GitHub search 0 hits',
        **dis[i],
        'accepted': False,
        'lean': {'literal_endpoint': None, 'kernel_checked': False, 'reason': 'Claude lane: Lean not run; no qualifying candidate'},
    }
open(D + '/results.json', 'x').write(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
from collections import Counter
print(len(out), Counter(v['outcome'] for v in out.values()))

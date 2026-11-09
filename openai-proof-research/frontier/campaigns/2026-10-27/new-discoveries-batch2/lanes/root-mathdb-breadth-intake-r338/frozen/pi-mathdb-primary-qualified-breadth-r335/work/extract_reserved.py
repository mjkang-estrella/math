#!/usr/bin/env python3
"""Extract the 50 reserved reserved-ID records (full statements) from hash-verified corpus chunks."""
from pathlib import Path
import hashlib, json

BASE = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2')
LANE = BASE / 'lanes/pi-mathdb-primary-qualified-breadth-r335'
R301 = BASE / 'lanes/pi-mathdb-full-corpus-inventory-r301'
R334 = BASE / 'lanes/root-mathdb-stack-intake-r334'

ids = json.loads((R334 / 'reserved-ids.json').read_text())['ids']
want = set(ids)
found = {}
for i in range(1, 21):
    p = R301 / f'corpus/mathdb-normalized-chunk-{i:04d}.jsonl'
    for line in p.open():
        if not line.strip():
            continue
        r = json.loads(line)
        if r.get('mathdb_id') in want:
            found[r['mathdb_id']] = {'chunk': p.name, 'record': r}

missing = [i for i in ids if i not in found]
out = LANE / 'sources/reserved-records.jsonl'
with out.open('w') as f:
    for i in ids:
        if i in found:
            f.write(json.dumps({'mathdb_id': i, 'chunk': found[i]['chunk'], 'record': found[i]['record']},
                               sort_keys=True) + '\n')

sums = LANE / 'work/reserved-extraction-sha256.txt'
h = hashlib.sha256(out.read_bytes()).hexdigest()
sums.write_text(f'{h}  {out.name}\n')
print(json.dumps({'extracted': len(found), 'missing': missing, 'sha256': h,
                  'bytes': out.stat().st_size}))

"""Display one predeclared passage; never declares it semantically read."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
S = ROOT / 'frontier/sources/i151_spatial_dynamical_percolation_continuation'
plan = json.loads((S / sys.argv[1]).read_bytes())
i = int(sys.argv[2])
r = plan[i]
b = (ROOT / r['path']).read_bytes()
assert hashlib.sha256(b).hexdigest() == r['sha256']
lines = b.decode().splitlines()
part = lines[r['start'] - 1:r['end']]
assert hashlib.sha256('\n'.join(part).encode()).hexdigest() == r['passage_sha256']
print(r['path'], 'RANGE', r['start'], r['end'])
for n, line in enumerate(part, r['start']):
    print(f'{n}: {line}')
print('END PASSAGE', i, 'ENDING', repr(r['ending']))

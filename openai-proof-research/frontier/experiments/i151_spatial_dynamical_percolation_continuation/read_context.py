"""Bounded semantic display, never an ancestor verifier or a reading certificate."""
import json, sys, hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
S = ROOT / 'frontier/sources/i151_spatial_dynamical_percolation_continuation'
plan = json.loads((S / 'context-reading-plan.json').read_bytes())
n = int(sys.argv[1])
cache = {}
last = None
for i in plan['chunks'][n]:
    g = plan['groups'][i]
    p = g['representative']['path']
    if p not in cache:
        cache[p] = (ROOT / p).read_text().splitlines()
    line = cache[p][g['representative']['line'] - 1]
    assert hashlib.sha256(line.encode()).hexdigest() == g['sha256']
    if p != last:
        print('SOURCE', p)
        last = p
    print(f"[{i}:{g['representative']['line']}] {line}")
print(f'END CHUNK {n}; last group {plan["chunks"][n][-1]}; total chunks {len(plan["chunks"])}')

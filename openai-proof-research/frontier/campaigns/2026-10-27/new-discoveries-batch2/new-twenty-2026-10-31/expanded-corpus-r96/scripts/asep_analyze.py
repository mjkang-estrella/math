"""Summarise candidate ASEP vertices: denominator, support size, stabiliser order in S_n (368807 diagnostics)."""
import sys, json, itertools
from fractions import Fraction
from math import lcm
sys.path.insert(0, __import__('os').path.dirname(__file__))
from asep import build
n = int(sys.argv[1]); arcs = build(n)[0]
rows = []
for f in sys.argv[2:]:
    d = json.load(open(f))
    for z in d.get('zero_vertices', []):
        X = [[Fraction(0)] * n for _ in range(n)]
        for t, (i, j) in enumerate(arcs): X[i][j] = Fraction(z[t]).limit_denominator(10000)
        D = lcm(*[v.denominator for r in X for v in r]); supp = sum(1 for r in X for v in r if v)
        stab = sum(1 for p in itertools.permutations(range(n)) if all(X[p[i]][p[j]] == X[i][j] for i in range(n) for j in range(n)))
        rows.append({'file': f, 'den': D, 'support': supp, 'stab': stab, 'X': [[str(v) for v in r] for r in X]})
rows.sort(key=lambda r: (-r['stab'], r['den'], r['support']))
seen = set(); out = []
for r in rows:
    k = json.dumps(r['X'])
    if k in seen: continue
    seen.add(k); out.append(r)
json.dump(out, open('outputs/asep/candidates-n%d.json' % n, 'w'), indent=0)
print(len(out), 'distinct'); 
for r in out[:8]: print(r['den'], r['support'], r['stab'])
from collections import Counter
print('den', Counter(r['den'] for r in out)); print('stab', Counter(r['stab'] for r in out)); print('supp', Counter(r['support'] for r in out))

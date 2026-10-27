import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from math import gcd
from gkn_tail2 import tail_components, contrib_series
import json, random

def margins(k, n, samples=20000):
    C, comps = tail_components(k, n)
    if not comps:
        return {"k":k,"n":n,"C":str(C),"min_tail":str(C),"act":[]}
    fs = {}
    for (c, s, bs, phi) in comps:
        fs[c] = contrib_series(c, s, bs, phi, c-1)
    L = 1
    for c in fs: L = L*c//gcd(L,c)
    if L <= 200000:
        best = min(C + sum(fs[c][m % c] for c in fs) for m in range(L))
    else:
        rnd = random.Random(1)
        best = None
        for _ in range(samples):
            m = rnd.randrange(L)
            t = C + sum(fs[c][m % c] for c in fs)
            if best is None or t < best: best = t
    return {"k":k,"n":n,"C":str(C),"min_tail":str(best),"act":sorted(fs)}

worst = []
for n in range(0, 26):
    for k in range(1, 60):
        r = margins(k, n)
        worst.append((F(r["min_tail"])/F(r["C"]), r))
worst.sort(key=lambda x: x[0])
print("Worst 20 by min_tail/C:")
for ratio, r in worst[:20]:
    print(f"k={r['k']:3d} n={r['n']:3d} C={r['C']:>12} min_tail={r['min_tail']:>10} ratio={float(ratio):.5f} act={r['act']}")
json.dump([[str(x[0]), x[1]] for x in worst[:200]], open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks/margins.json','w'), indent=1)

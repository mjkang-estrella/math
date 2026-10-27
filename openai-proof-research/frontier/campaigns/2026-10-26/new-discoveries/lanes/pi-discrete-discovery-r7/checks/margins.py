import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from math import gcd
from gkn_tail2 import tail_components, contrib_series
import json

def margins(k, n):
    m0 = n*(2*k+n-2)
    C, comps = tail_components(k, n)
    fs = {}
    for (c, s, bs, phi) in comps:
        fs[c] = contrib_series(c, s, bs, phi, c-1)
    if not fs:
        return {"k":k,"n":n,"C":str(C),"min_tail":str(C),"comps":[]}
    L = 1
    for c in fs: L = L*c//gcd(L,c)
    best = None; bestm = None
    for m in range(L):
        t = C + sum(fs[c][m % c] for c in fs)
        if best is None or t < best: best, bestm = t, m
    return {"k":k,"n":n,"C":str(C),"min_tail":str(best),"m":bestm,
            "comps":[(c, [str(x) for x in fs[c]]) for c in sorted(fs)]}

worst = []
for n in range(0, 41):
    for k in range(1, 80):
        r = margins(k, n)
        ratio = F(r["min_tail"])/F(r["C"])
        worst.append((ratio, r))
worst.sort(key=lambda x: x[0])
print("Worst 15 by min_tail/C ratio:")
for ratio, r in worst[:15]:
    print(f"k={r['k']} n={r['n']} C={r['C']} min_tail={r['min_tail']} ratio={float(ratio):.4f} comps={[c for c,_ in r['comps']]}")
json.dump([[str(x[0]), x[1]] for x in worst[:100]], open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks/margins.json','w'), indent=1)

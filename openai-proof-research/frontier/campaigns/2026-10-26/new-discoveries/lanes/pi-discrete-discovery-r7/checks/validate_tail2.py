import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from gkn_tail2 import tail_series, gkn_ND, series_div_frac

def check(k, n, extra=200):
    m0 = n*(2*k+n-2)
    M = m0 + extra
    t, C, comps = tail_series(k, n, M)
    N, D = gkn_ND(k, n)
    c = series_div_frac(N, D, M)
    bad = None
    for m in range(m0, M+1):
        if t[m] != c[m]:
            bad = (m, t[m], c[m]); break
    print(f"k={k} n={n}: {'OK' if bad is None else f'FAIL {bad}'}; C={C}; comps={[(cc,s) for cc,s,_,_ in comps]}")
    return bad is None

allok = True
for (k,n) in [(4,2),(5,3),(6,4),(7,3),(10,5),(8,6),(12,7),(3,4),(2,5),(5,8),(9,9),(15,4),(6,12),(20,3),(11,11)]:
    allok &= check(k,n)
print("ALL OK" if allok else "SOME FAIL")

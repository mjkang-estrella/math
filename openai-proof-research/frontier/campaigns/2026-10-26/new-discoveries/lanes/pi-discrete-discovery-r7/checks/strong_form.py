"""Check: for k>=2, are ALL coefficients of G_{k,n} >= 1 (i.e. G - 1/(1-q) >= 0)?"""
import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from fractions import Fraction as F
from gkn_tail2 import gkn_ND, series_div_frac, tail_components, contrib_series
from math import gcd

def min_coeff(k, n, cap=40000):
    m0 = n*(2*k+n-2)
    N, D = gkn_ND(k, n)
    M = min(m0-1, cap)
    mn = None
    if M >= 0:
        c = series_div_frac(N, D, M)
        mn = min(c)
        if mn < 1:
            return ("initial", c.index(mn), str(mn))
    # tail
    C, comps = tail_components(k, n)
    fs = {}
    for (cc, s, bs, phi) in comps:
        fs[cc] = contrib_series(cc, s, bs, phi, cc-1)
    L = 1
    for cc in fs: L = L*cc//gcd(L, cc)
    if L <= 3000000:
        tmin = min(C + sum(fs[cc][m % cc] for cc in fs) for m in range(L))
    else:
        import random; rnd = random.Random(7)
        tmin = None
        for _ in range(50000):
            m = rnd.randrange(L)
            t = C + sum(fs[cc][m % cc] for cc in fs)
            if tmin is None or t < tmin: tmin = t
    if tmin < 1:
        return ("tail", None, str(tmin))
    return ("ok", None, str(tmin if mn is None else min(mn, tmin)))

bad = 0
for n in range(0, 31):
    for k in range(2, 101):
        r = min_coeff(k, n)
        if r[0] != "ok":
            print("VIOLATION k,n:", k, n, r); bad += 1
    print(f"n={n} done, violations={bad}")
print("Strong form (all coeffs >= 1 for k>=2):", "FAILED" if bad else "NO violations found (k<=100, n<=30)")

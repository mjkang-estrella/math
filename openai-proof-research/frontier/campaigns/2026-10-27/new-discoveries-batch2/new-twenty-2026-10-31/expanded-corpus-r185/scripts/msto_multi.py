"""Exact mean subtree order for complete multipartite graphs K_{n_1,...,n_k} and the effect of adding an edge inside part j.
Induced subgraph on a vertex set with part counts s_i is complete multipartite; tau = s^{k'-2} prod_i (s-s_i)^{s_i-1}
(k' = number of nonzero s_i, s = sum s_i); k'=1: tau = 1 iff s = 1.
Usage: msto_multi.py n1,n2,...   [also accepts a list of specs separated by spaces]
"""
import sys, itertools
from math import comb, prod
from fractions import Fraction

def tau(s):
    nz = [x for x in s if x]
    S = sum(nz); k = len(nz)
    if k == 0: return 0
    if k == 1: return 1 if S == 1 else 0
    return S ** (k - 2) * prod((S - x) ** (x - 1) for x in nz)

def analyze(parts):
    k = len(parts)
    comps = list(itertools.product(*[range(n + 1) for n in parts]))
    tw = {s: tau(s) for s in comps}
    N = R = 0
    for s in comps:
        t = tw[s]
        if t:
            c = prod(comb(parts[i], s[i]) for i in range(k)) * t
            N += c; R += c * sum(s)
    mu = Fraction(R, N)
    res = {}
    for j in range(k):
        if parts[j] < 2 or j in [jj for jj in range(j) if parts[jj] == parts[j]]: continue
        A = B = 0
        for s1 in comps:
            if s1[j] < 1: continue
            t1 = tw[s1]
            if not t1: continue
            for s2 in comps:
                if s2[j] < 1: continue
                ok = True
                for i in range(k):
                    if s1[i] + s2[i] > parts[i]: ok = False; break
                if not ok: continue
                t2 = tw[s2]
                if not t2: continue
                # choose S (contains u, not v) and S' (contains v, not u), disjoint
                c = 1
                for i in range(k):
                    if i == j:
                        c *= comb(parts[i] - 2, s1[i] - 1) * comb(parts[i] - 2 - (s1[i] - 1), s2[i] - 1)
                    else:
                        c *= comb(parts[i], s1[i]) * comb(parts[i] - s1[i], s2[i])
                w = c * t1 * t2
                A += w; B += w * (sum(s1) + sum(s2))
        res[parts[j]] = Fraction(R + B, N + A) - mu
    return mu, res

if __name__ == '__main__':
    for spec in sys.argv[1:]:
        parts = tuple(int(x) for x in spec.split(','))
        mu, res = analyze(parts)
        allneg = all(d <= 0 for d in res.values()) and res
        print(spec, f'mu={float(mu):.5f}', {p: f'{float(d):+.3e}' for p, d in res.items()}, 'COUNTEREXAMPLE' if allneg else '', flush=True)

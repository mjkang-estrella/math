# Consistency checks at (3,20,2,19), written from source definitions; imports only the reviewer's own module (same dir).
import sys, json, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from smyth_review import type_counts, dom, Dinic
from fractions import Fraction
from math import comb, factorial
A, a, B, b = 3, 20, 2, 19
X, Y, _ = type_counts(A, a, B, b)
def weight(p, lam):
    w = Fraction(1)
    for x in lam: w *= p(x)
    return w
seqs = {'poisson 1/n!': lambda n: Fraction(1, factorial(n)),
        'binomial C(40,n)': lambda n: Fraction(comb(40, n)),
        'geometric 2^-n': lambda n: Fraction(1, 2**n),
        'uniform 1 (constant)': lambda n: Fraction(1),
        'C(5,n) (finite support)': lambda n: Fraction(comb(5, n))}
out = {}
for name, p in seqs.items():
    lhs = sum(m * weight(p, t) for t, m in X.items()); rhs = sum(m * weight(p, t) for t, m in Y.items())
    out[name] = {'(p^A)_b (p^B)_a <= (p^A)_a (p^B)_b': lhs <= rhs, 'ratio_lhs_over_rhs': float(lhs / rhs) if rhs else None}
# reversed orientation (image dominates source) for contrast
xs, ys = sorted(X), sorted(Y); n = 2 + len(xs) + len(ys); D = Dinic(n)
for i, p in enumerate(xs):
    D.add(0, 2 + i, X[p])
    for j, q in enumerate(ys):
        if dom(q, p): D.add(2 + i, 2 + len(xs) + j, 1 << 50)
for j, q in enumerate(ys): D.add(2 + len(xs) + j, 1, Y[q])
sys.setrecursionlimit(10000)
out['reversed_orientation_max_matching'] = D.maxflow(0, 1); out['|X|'] = sum(X.values())
print(json.dumps(out, indent=1))

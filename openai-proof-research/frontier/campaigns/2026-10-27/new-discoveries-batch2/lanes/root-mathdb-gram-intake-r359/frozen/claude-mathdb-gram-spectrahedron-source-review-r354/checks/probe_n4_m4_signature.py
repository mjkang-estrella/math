"""EXPLORATORY bounded probe (instance-level, no credit): n = m = 4.

For 4 quaternary integer quadrics with dim (q)_4 = 34 (so I_4^perp = R E is 1-dim),
compute the exact inertia of the 10x10 moment matrix M_E[a][b] = E(v_a v_b).
M_E kills U = span(q_i); it is (up to sign) PSD with kernel exactly U iff inertia is (6,0,4) or (0,6,4).
Such a sample, plus independence of the 10 products q_i q_j, is an exact dual certificate that
Gram(sum q_i^2) is a singleton (see SUMMARY.md, Lemma D). Records the inertia histogram only.
Exit 0 on completion (the probe asserts nothing about the outcome).
"""
import json
import random
import sys
from collections import Counter
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gramlib import quad_monomials, quartic_monomials, add, nullspace_Q, inertia_symmetric, rank_mod_p

n = 4
v = quad_monomials(n)
quart = quartic_monomials(n)
qi = {e: i for i, e in enumerate(quart)}
P = 2**31 - 1
samples = int(sys.argv[1]) if len(sys.argv) > 1 else 60
bound = int(sys.argv[2]) if len(sys.argv) > 2 else 3
rng = random.Random(404067)
hist = Counter()
witness = None
for s in range(samples):
    qs = [[rng.randint(-bound, bound) for _ in v] for _ in range(4)]
    rows = []
    for q in qs:
        for g in v:
            row = [0] * len(quart)
            for c, e in zip(q, v):
                row[qi[add(e, g)]] += c
            rows.append(row)
    ker = nullspace_Q(rows, len(quart))
    if len(ker) != 1:
        hist['dim_I4_perp=%d' % len(ker)] += 1
        continue
    E = ker[0]
    M = [[E[qi[add(a, b)]] for b in v] for a in v]
    # sanity: M q = 0 for each q
    for q in qs:
        assert all(sum(M[r][c] * q[c] for c in range(len(v))) == 0 for r in range(len(v)))
    inr = inertia_symmetric(M)
    hist[str(inr)] += 1
    if witness is None and inr in ((6, 0, 4), (0, 6, 4)):
        prods = []
        for i in range(4):
            for j in range(i, 4):
                row = [0] * len(quart)
                for ci, ei in zip(qs[i], v):
                    for cj, ej in zip(qs[j], v):
                        row[qi[add(ei, ej)]] += ci * cj
                prods.append(row)
        witness = {'q_coeffs_in_basis': [list(map(str, v))] + qs, 'inertia': inr,
                   'products_rank_mod_p': rank_mod_p(prods, P)}
print(json.dumps({'samples': samples, 'coef_bound': bound, 'inertia_histogram': dict(hist),
                  'definite_witness': witness}, indent=1))

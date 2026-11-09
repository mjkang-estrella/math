"""Independent rational checks, not a universal nonexistence certificate.

Checks the explicit 20-dimensional prior-method adaptation and coordinate chart.
Only Python standard library; no floating-point computations.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import random

BASE = Path(__file__).resolve().parents[1]

def rank(rows):
    a = [[F(x) for x in row] for row in rows]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        c = a[r][j]
        a[r] = [x/c for x in a[r]]
        for i in range(len(a)):
            if i != r:
                c = a[i][j]
                a[i] = [x-c*y for x,y in zip(a[i],a[r])]
        r += 1
        if r == len(a):
            break
    return r

edges = list(combinations(range(6), 2))
central = edges[1:]
omega = [int(e in [(0,1),(2,3),(4,5)]) for e in edges]
quotient = [[int(e == f) - int(e == (0,1) and f in [(2,3),(4,5)])
             for e in edges] for f in central]
assert all(sum(a*b for a,b in zip(row,omega)) == 0 for row in quotient)
assert rank(quotient) == 14
skew = [[0]*6 for _ in range(6)]
for (i,j), c in zip(edges,omega):
    skew[i][j], skew[j][i] = c, -c
assert rank(skew) == 6

zero = (0,)*20
basis = [tuple(int(i == j) for j in range(20)) for i in range(20)]
def bracket(x,y):
    wedge = [x[i]*y[j]-x[j]*y[i] for i,j in edges]
    return (0,)*6 + tuple(sum(a*b for a,b in zip(row,wedge)) for row in quotient)

table = [[bracket(x,y) for y in basis] for x in basis]
for i,j in product(range(20), repeat=2):
    assert table[i][j] == tuple(-x for x in table[j][i])
assert all(table[i][i] == zero for i in range(20))
for i,j,k in product(range(20), repeat=3):
    terms = [bracket(basis[i],table[j][k]), bracket(basis[j],table[k][i]),
             bracket(basis[k],table[i][j])]
    assert tuple(map(sum,zip(*terms))) == zero
    assert terms[0] == zero  # class at most two, independently of Jacobi
assert any(table[i][j] != zero for i,j in product(range(20),repeat=2))
assert rank([list(table[i][j]) for i,j in product(range(20),repeat=2)]) == 14

# Independent formula check: transform an arbitrary monomial bracket by
# computing bilinearly with all ordered pairs, then compare the sparse chart.
rng = random.Random(372720)
e8 = list(combinations(range(8),2))
def invertible(n):
    while True:
        a = [[F(rng.randrange(-4,5),rng.randrange(1,5)) for _ in range(n)]
             for _ in range(n)]
        if rank(a) == n:
            return a

for trial in range(10):
    R, Q = invertible(8), invertible(4)
    delta = [rng.randrange(4) for _ in e8]
    c = [F(rng.randrange(-4,5),rng.randrange(1,5)) for _ in e8]
    monomial = [[[F(0)]*4 for _ in range(8)] for _ in range(8)]
    for e, (i,j) in enumerate(e8):
        monomial[i][j][delta[e]] = c[e]
        monomial[j][i][delta[e]] = -c[e]
    for k, (a,b) in product(range(4), e8):
        direct = sum(Q[k][l]*R[i][a]*R[j][b]*monomial[i][j][l]
                     for i,j,l in product(range(8),range(8),range(4)))
        chart = sum(Q[k][delta[e]]*c[e]*(R[i][a]*R[j][b]-R[j][a]*R[i][b])
                    for e,(i,j) in enumerate(e8))
        assert direct == chart

out = dict(status='PASS_EXACT_FINITE_CHECKS', arithmetic='fractions.Fraction and integers',
           explicit_algebra_dimension=20, derived_dimension=14, nilpotency_class=2,
           jacobi_basis_triples=8000, defining_relation_skew_rank=6,
           chart_trials=10, chart_coordinates_checked=1120,
           universal_nonexistence_formally_certified=False,
           notice='Universal rank and basis arguments are in PRIOR_METHOD.md; these finite checks are not a Lean proof.')
(BASE/'verification'/'exact-result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

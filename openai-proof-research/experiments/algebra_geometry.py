"""Exact finite sanity checks for proposals/algebra_geometry.md.
No external packages. These checks do not replace the general proofs.
"""
from fractions import Fraction as Q
from itertools import product

# F = uv - ((x*x-a)**2 + t**4). Exact Jacobian and rational chart.
grid = sorted({Q(p, q) for p in range(-3, 4) for q in range(1, 4)})
checks = 0
for a in (1, 2):
    singular_x = set()
    for x, t, u, v in product(grid, repeat=4):
        s = (x*x-a)**2 + t**4
        f = u*v-s
        grad = (-4*x*(x*x-a), -4*t**3, v, u)
        singular = f == 0 and all(d == 0 for d in grad)
        encoded = x*x == a and t == u == v == 0
        assert singular == encoded
        if singular:
            singular_x.add(x)
        checks += 1
    assert singular_x == ({Q(-1), Q(1)} if a == 1 else set())
    for x, t, u in product(grid, repeat=3):
        if u:
            v = ((x*x-a)**2+t**4)/u
            assert u*v-((x*x-a)**2+t**4) == 0
            assert u != 0  # partial F / partial v: chart is smooth
print(f'PASS: {checks} exact rational Jacobian tests and rational-chart checks')

# Universal relation ab=1, without ba=1. Normal forms b^i a^j.
# Coefficients in F_2, so finite polynomials are sets of monomials.
def mul(p, q):
    out = set()
    for i,j in p:
        for k,l in q:
            c = min(j,k)
            term = (i+k-c,j+l-c)
            if term in out: out.remove(term)
            else: out.add(term)
    return out
one={(0,0)}; a={(0,1)}; b={(1,0)}; e={(0,0),(1,1)}
assert mul(a,b)==one and mul(b,a)!=one
assert mul(e,e)==e and not mul(a,e) and not mul(e,b)
def E(i,j): return mul(mul({(i,0)},e),{(0,j)})
for i,j,k,l in product(range(6),repeat=4):
    assert mul(E(i,j),E(k,l)) == (E(i,l) if j==k else set())
print('PASS: 1296 matrix-unit identities in the universal one-sided-inverse algebra')

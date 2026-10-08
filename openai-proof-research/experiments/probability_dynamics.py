"""Exact local checks for proposals/probability_dynamics.md; standard library only.

These verify downstream commutator algebra, not the assumed upstream gap.
Rational spin matrices are similar to the usual self-adjoint spin-one matrices.
"""
from fractions import Fraction as F
from math import log, sqrt


def add(a, b):
    return [[x + y for x, y in zip(r, s)] for r, s in zip(a, b)]


def scale(c, a):
    return [[c * x for x in r] for r in a]


def mul(a, b):
    return [[sum(x * y for x, y in zip(r, c)) for c in zip(*b)] for r in a]


def comm(a, b):
    return add(mul(a, b), scale(-1, mul(b, a)))


def kron(a, b):
    return [[x * y for x in r for y in s] for r in a for s in b]


def diag(v):
    return [[x if i == j else F(0) for j in range(len(v))] for i, x in enumerate(v)]


z = diag([F(1), F(0), F(-1)])
ident = diag([F(1)] * 3)
plus = [[F(0), F(2), F(0)], [F(0), F(0), F(2)], [F(0)] * 3]
minus = [[F(0)] * 3, [F(1), F(0), F(0)], [F(0), F(1), F(0)]]
assert comm(plus, minus) == scale(2, z)
assert add(mul(z, z), scale(F(1, 2), add(mul(plus, minus), mul(minus, plus)))) == scale(2, ident)
xy = scale(F(1, 2), add(kron(plus, minus), kron(minus, plus)))
h = add(kron(z, z), xy)
for a, b in [(1, 0), (0, 1), (1, 1), (2, -3)]:
    q = add(scale(a, kron(z, ident)), scale(b, kron(ident, z)))
    assert comm(q, comm(h, q)) == scale(-(a-b)**2, xy)
for r in [F(2), F(3, 2), F(1, 2)]:
    exponential = kron(diag([r, F(1), 1/r]), ident)
    rhs = scale(-(r + 1/r - 2), mul(mul(exponential, xy), exponential))
    assert comm(exponential, comm(h, exponential)) == rhs
# The minimal polynomial implies the XY eigenvalues are among 0, +/-1, +/-sqrt(2).
xy2 = mul(xy, xy)
xy3 = mul(xy2, xy)
xy5 = mul(mul(xy3, xy), xy)
assert add(add(xy5, scale(-3, xy3)), scale(2, xy)) == scale(0, xy)
delta = log(20)/784
tau = sqrt(delta/sqrt(2))
print('PASS: spin normalization; weighted and exponential double commutators; XY polynomial')
print(f'delta = {delta:.12g}; tau = {tau:.12g}; block variance bound = {4/(3*delta):.12g}')

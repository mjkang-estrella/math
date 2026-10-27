#!/usr/bin/env python3
"""Exact checks of two already-uncountable Clarkson counterexamples.

No floating-point arithmetic enters any certificate assertion.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import sympy as s


def root_interval(x, n, denominator=10**6):
    assert x >= 0
    low, high = 0, denominator * (int(x) + 2)
    while high - low > 1:
        mid = (low + high) // 2
        if F(mid, denominator) ** n <= x:
            low = mid
        else:
            high = mid
    a, b = F(low, denominator), F(high, denominator)
    assert a**n <= x < b**n
    return a, b


A = s.Matrix([[1, -3], [3, -7]])
B = s.Matrix([[7, 3], [-3, -1]])
C = s.Matrix([[-1, -3], [3, 7]])
lam = s.Symbol('lam')
for X in [A, B, C, A+B+C]:
    assert (X.T*X).charpoly(lam).as_expr() == lam**2-68*lam+4
assert (A+B).T*(A+B) == 64*s.eye(2)
assert (B+C).T*(B+C) == 36*s.eye(2)
assert (C+A).T*(C+A) == 36*s.eye(2)
# Singular values of the four equal-spectrum matrices are 3*sqrt(2) +/- 4.
rt2 = root_interval(F(2), 2)
sl, su = 3*rt2[0]-4, 3*rt2[1]-4
tl, tu = 3*rt2[0]+4, 3*rt2[1]+4
assert 0 < sl < su < tl < tu
lhs_lower = 4*(sl**2*root_interval(sl,4)[0] + tl**2*root_interval(tl,4)[0])
rhs_upper = ((3*root_interval(F(3),4)[1]+1)/(4*root_interval(F(2),4)[0])
             * (128*root_interval(F(8),4)[1]+144*root_interval(F(6),4)[1]))
assert lhs_lower > 460 and rhs_upper < 459

# Independent exact check of the earlier public rank-one witness.
P = s.diag(1, 0)
Q = s.diag(0, 1)
R = -s.ones(2)/2
for X in [P, Q, R, P+Q+R]:
    assert (X.T*X).charpoly(lam).as_expr() == lam**2-lam
assert (P+Q).T*(P+Q) == s.eye(2)
assert (Q+R).T*(Q+R) == s.eye(2)/2
assert (R+P).T*(R+P) == s.eye(2)/2
prior_rhs_upper = ((3*root_interval(F(3),4)[1]+1)/(4*root_interval(F(2),4)[0])
                   * (2+root_interval(F(128),8)[1]))
assert prior_rhs_upper < 4

result = {
    'status': 'PASS exact arithmetic; no discovery credit',
    'own_integer_witness': [list(map(list, [list(A.row(i)) for i in range(2)])),
                            list(map(list, [list(B.row(i)) for i in range(2)])),
                            list(map(list, [list(C.row(i)) for i in range(2)]))],
    'exponent': '9/4',
    'own_lhs_lower': str(lhs_lower), 'own_rhs_upper': str(rhs_upper),
    'own_certified_gap_lower': str(lhs_lower-rhs_upper),
    'prior_rhs_upper': str(prior_rhs_upper),
    'reason_uncredited': 'Same source conjecture publicly refuted on 2026-10-26',
}
output = json.dumps(result, indent=2, default=int)+'\n'
Path(__file__).with_name('exact-check.json').write_text(output)
print(output, end='')

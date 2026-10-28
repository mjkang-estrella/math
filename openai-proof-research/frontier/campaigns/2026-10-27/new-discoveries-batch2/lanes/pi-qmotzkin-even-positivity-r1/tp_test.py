#!/usr/bin/env python3
"""Test total positivity (over Z>=0[q]) of the Krylov matrix
U_{h,i} = (B^i)_{h,0} = sum over walks 0->h of length i of q^{sum of source heights}.

If all minors of U lie in Z>=0[q], then
  Delta_n^{(2k)} = sum_S q^{sum S} det(U_S)^2  in Z>=0[q],
proving Conjecture A.4. Also verify this square-sum identity itself.
"""
from compute import M, padd, pmul, pstr, pzero, poly_divexact, hankel_det
from itertools import combinations

IMAX = 12  # columns (lengths) 0..IMAX-1
HMAX = IMAX + 2

# W_h(i) = (B^i)_{h,0}: iterate columns
W = [[None] * IMAX for _ in range(HMAX)]
for h in range(HMAX):
    W[h][0] = {0: 1} if h == 0 else {}
for i in range(IMAX - 1):
    for h in range(HMAX):
        acc = {}
        for hp in (h - 1, h, h + 1):
            if 0 <= hp < HMAX and W[hp][i]:
                acc = padd(acc, pmul({hp: 1}, W[hp][i]))
        W[h][i + 1] = acc

# sanity: W[0][i] should equal M_i
for i in range(min(IMAX, 10)):
    assert W[0][i] == M[i], f"W_0({i}) != M_{i}: {pstr(W[0][i])} vs {pstr(M[i])}"
print("W_0(i) = M_i verified for i<10")

def minor(rows, cols):
    m = len(rows)
    A = [[W[r][c] for c in cols] for r in rows]
    prev = {0: 1}
    sign = 1
    for k in range(m - 1):
        if A[k][k] == {}:
            for i2 in range(k + 1, m):
                if A[i2][k] != {}:
                    A[k], A[i2] = A[i2], A[k]
                    sign = -sign
                    break
            else:
                return {}
        for i2 in range(k + 1, m):
            for j in range(k + 1, m):
                num = padd(pmul(A[k][k], A[i2][j]),
                           {e: -c for e, c in pmul(A[i2][k], A[k][j]).items()})
                A[i2][j] = num if k == 0 else poly_divexact(num, prev)
        prev = A[k][k]
    return {e: c * sign for e, c in A[m - 1][m - 1].items()}

print("\n=== All minors of U (rows, cols <= 7), size <= 4: coefficientwise? ===")
bad = 0
tested = 0
for m in range(1, 5):
    for rows in combinations(range(7), m):
        for cols in combinations(range(7), m):
            d = minor(rows, cols)
            tested += 1
            if d and not pzero(d):
                bad += 1
                if bad <= 10:
                    print(f"NEGATIVE-COEFF minor rows={rows} cols={cols}: {pstr(d)}")
print(f"tested {tested} minors, {bad} with negative coefficients")

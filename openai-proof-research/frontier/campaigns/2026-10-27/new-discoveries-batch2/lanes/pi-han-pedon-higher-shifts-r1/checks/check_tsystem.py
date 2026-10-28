"""Exact verification of the Hankel T-system for Phi_1 coefficients:
Delta_{k+1}^(s) * Delta_{k-1}^(s+2) = Delta_k^(s) * Delta_k^(s+2) - (Delta_k^(s+1))^2.
(Theorem 1 of FINDINGS.md; classical Desnanot-Jacobi. Consistency check only.)"""
import sys
sys.path.insert(0, '.')
from metallic import phi_coeffs
from fractions import Fraction as Fr

def bareiss(M):
    n = len(M)
    if n == 0: return 1
    M = [[Fr(x) for x in row] for row in M]
    prev = Fr(1); sign = 1
    for r in range(n - 1):
        if M[r][r] == 0:
            for i in range(r + 1, n):
                if M[i][r] != 0:
                    M[r], M[i] = M[i], M[r]; sign = -sign; break
            else:
                return 0
        for i in range(r + 1, n):
            for j in range(r + 1, n):
                M[i][j] = (M[i][j] * M[r][r] - M[i][r] * M[r][j]) / prev
        prev = M[r][r]
    return sign * M[n - 1][n - 1]

n = 1
f = phi_coeffs(n, 120)
def D(s, k):
    return bareiss([[f[s + a + b] for b in range(k)] for a in range(k)])

bad = 0
for s in range(0, 8):
    for k in range(1, 7):
        lhs = D(s, k + 1) * D(s + 2, k - 1)
        rhs = D(s, k) * D(s + 2, k) - D(s + 1, k) ** 2
        if lhs != rhs:
            bad += 1
            print("FAIL", s, k, lhs, rhs)
print("T-system:", "ALL OK (48 identities)" if bad == 0 else f"{bad} FAILURES")

"""Collect Delta_j^(ell)(Phi_n) over long ranges via H-fraction data; validate
against direct Bareiss determinants; fit residue subsequences mod rho_n."""
import sys
sys.path.insert(0, '.')
from metallic import *
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

def full_det_seq(n, ell, steps, N=2000):
    """Returns dict j->Delta_j^(ell)(Phi_n) for j up to ~s_max from H-fraction."""
    data, Ds = hfraction(n, ell, steps, N=N)
    det, s = determinants(data)
    return det, s, data

def validate(n, ell, steps, N, jmax):
    det, s, data = full_det_seq(n, ell, steps, N)
    f = phi_coeffs(n, ell + 2 * jmax + 5)
    ok = True
    for j in list(range(0, jmax + 1)):
        mat = [[f[ell + a + b] for b in range(j)] for a in range(j)]
        d = bareiss(mat)
        d2 = det.get(j, 0)
        if d != d2:
            print(f"  MISMATCH n={n} ell={ell} j={j}: bareiss={d} hfraction={d2}")
            ok = False
    print(f"validate n={n} ell={ell} j<= {jmax}: {'OK' if ok else 'FAIL'}")
    return ok

if __name__ == '__main__':
    validate(1, 4, 40, 800, 25)
    validate(1, 5, 40, 800, 25)
    validate(2, 5, 40, 900, 20)
    validate(3, 6, 40, 1000, 15)

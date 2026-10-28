"""Generates ../notes/conjectureC-data.json.

For each (n, ell): runs NextABC on the exact shift triple of Phi_n^(ell), extracts ALL
Delta_j^(ell) for j <= jmax (from the (sigma_j, v_j) data via Han16 Thm 2.2), groups by
residue mod rho_n, detects exact polynomial fits by finite differences, and records
degree, point count, binomial-basis coefficients, and a sympy factorization.

All determinant values were separately cross-validated against direct Bareiss integer
determinants (see collect.validate); jobs kept below the ranges where that was done.
"""
import sys, json, math
sys.path.insert(0, '.')
from collect import full_det_seq
from sympy import symbols, factor, Rational, expand

def rho(n): return 2*n*(n+1) if n % 2 == 0 else 4*n*(n+1)

def collect(n, ell, steps, N, dmax):
    det, s, data = full_det_seq(n, ell, steps, N)
    smax = s[-1]; R = rho(n)
    sj_set = {sv: det[sv] for sv in s}
    m = symbols('m')
    out = {"n": n, "ell": ell, "rho": R, "jmax": smax, "steps": len(s), "classes": {}}
    for r in range(R):
        vs = [int(sj_set.get(j, 0)) for j in range(r, smax + 1, R)]
        deg = None
        for d in range(0, dmax + 1):
            diff = vs[:]
            for _ in range(d):
                diff = [diff[i + 1] - diff[i] for i in range(len(diff) - 1)]
            if diff and all(x == diff[0] for x in diff) and len(vs) > d + 3:
                deg = d
                tmp = vs[:d + 1]; coeffs = []
                for i in range(d + 1):
                    coeffs.append(int(tmp[0]))
                    tmp = [tmp[k + 1] - tmp[k] for k in range(len(tmp) - 1)]
                expr = 0
                for i, c in enumerate(coeffs):
                    num = Rational(1)
                    for t in range(i):
                        num = num * (m - t)
                    expr += Rational(c) * num / Rational(math.factorial(i))
                out["classes"][r] = {"degree": d, "npts": len(vs),
                                     "binomial_coeffs": coeffs,
                                     "factored": str(factor(expand(expr)))}
                break
        if deg is None:
            out["classes"][r] = {"degree": None, "npts": len(vs), "first6": vs[:6]}
    return out

jobs = [(1, 4, 60, 1000, 2), (1, 5, 300, 8000, 3), (1, 6, 300, 8000, 5),
        (1, 7, 420, 12000, 7), (1, 8, 420, 12000, 10), (2, 5, 300, 9000, 3),
        (2, 6, 300, 9000, 4), (2, 7, 300, 9000, 5), (3, 6, 300, 9000, 4),
        (3, 7, 400, 12000, 4)]

if __name__ == '__main__':
    results = []
    for (n, ell, steps, N, dmax) in jobs:
        results.append(collect(n, ell, steps, N, dmax))
        print("done", n, ell, flush=True)
    json.dump(results, open('../notes/conjectureC-data.json', 'w'), indent=1)
    print("saved")

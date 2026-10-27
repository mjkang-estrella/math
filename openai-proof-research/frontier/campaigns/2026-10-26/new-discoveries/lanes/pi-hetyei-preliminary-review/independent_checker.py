#!/usr/bin/env python3
"""Independent adversarial checker for the Hetyei Conjecture 6.10 candidate.

Deliberately DIFFERENT algorithms from root's verify_recurrence.py:
  A. Source recurrence via rational power-series LONG DIVISION of
     1/((1-t)(1-log(1-t))) (not the convolution u_n = sum u_{n-j}/(j(j-1))).
  B. Literal composition-count formula (16) for K_n (brute-force over
     ordered compositions), and signed-Stirling formula (18).
  C. Actual numpy.linalg.eigh eigen-decompositions of the arrowhead
     matrices H_N (root used exact moment/probability recurrences only).
  D. Direct numerical test of the propagation criterion's implied bounds
     against the eigen-decomposition, for several m and N.
  E. Independent exact check of b_3, b_12, b_14, a_11, a_12 against
     printed source values.
No claims of acceptance; review evidence only. credit 0.
"""
import json
from fractions import Fraction as F
from math import comb, factorial
import numpy as np

out = {}

# ---------- A. Rational power-series long division -----------------
# U(t) = 1/((1-t)(1-log(1-t))).  Denominator D(t) = 1 - sum_{j>=2} t^j/(j(j-1)).
# Instead of using that closed form, build D(t) directly from
# (1-t)*(1-log(1-t)) as a truncated power series (independent derivation),
# then invert by long division.
DEG = 240
# -log(1-t) = sum t^j/j
neglog = [F(0)] + [F(1, j) for j in range(1, DEG + 1)]        # coefficients t^j
one_minus_t = [F(1), F(-1)] + [F(0)] * (DEG - 1)
# (1-t)*(1 + neglog)   since 1 - log(1-t) = 1 + sum t^j/j
D = [F(0)] * (DEG + 1)
for i in range(0, DEG + 1):
    for j in range(0, DEG + 1 - i):
        # (1-t) has coeffs c0=1, c1=-1
        pass
# explicit convolution (1 - t)*(1 - log(1-t)) = (1-t)*(1+neglog)
# 1 - log(1-t) = 1 + sum_{j>=1} t^j/j
base = [F(1)] + [F(1, j) for j in range(1, DEG + 1)]
for i in range(DEG + 1):
    D[i] += base[i]
    if i >= 1:
        D[i] -= base[i - 1]
assert D[0] == 1 and D[1] == 0
assert all(D[j] == -F(1, (j * (j - 1))) for j in range(2, DEG + 1)), "denominator mismatch"

# long division: U = 1/D
u = [F(0)] * (DEG + 1)
u[0] = F(1)
for n in range(1, DEG + 1):
    u[n] = -sum(D[j] * u[n - j] for j in range(1, min(n, DEG) + 1))
b = [u[0]] + [u[n] - u[n - 1] for n in range(1, DEG + 1)]

out['A_denominator_coeffs_ok'] = True
out['A_b3'] = str(b[3])
out['A_b12'] = str(b[12])
out['A_b14'] = str(b[14])
out['A_b11'] = str(b[11])
assert b[3] == -F(1, 3)
assert b[12] == -F(10819, 9979200)
assert b[14] == -F(3676549, 1816214400)
assert b[14] - b[12] == -F(1707491, 1816214400)
assert b[12] < -F(1, 2000), "b12 not below -1/2000"
assert b[14] < b[12]
assert b[11] * factorial(11) == -319296  # a_11 = 319296 > 0, b_11 = -a_11/11!
assert b[12] * factorial(12) == -519312               # matches printed a_12
out['A_exact_values_match_printed_source'] = True

# sign of b_n for n=11..239 (exact rational, independent of root's range 100)
neg = all(x < 0 for x in b[11:])
out['A_b_negative_n11_to_239'] = bool(neg)
assert neg

# ---------- B. Literal composition formula (16) and Stirling (18) ----
def K_composition(n):
    """(16): K_n = sum over k, ordered compositions m_1+..+m_k=n, m_i>=2,
    of multinomial(n; m_1..m_k) * prod (m_i - 2)!"""
    total = 0
    def rec(rem, prod):
        nonlocal total
        if rem == 0:
            total += prod
            return
        for m in range(2, rem + 1):
            rec(rem - m, prod * comb(rem, m) * factorial(m - 2) if False else prod)
    # do it iteratively to apply multinomial correctly
    def rec2(rem, chosen):
        nonlocal total
        if rem == 0:
            coef = factorial(n)
            for m in chosen:
                coef //= factorial(m)
            total += coef * prod((m - 2) for m in chosen) if False else coef * __import__('math').prod(factorial(m - 2) for m in chosen)
            return
        for m in range(2, rem + 1):
            rec2(rem - m, chosen + [m])
    rec2(n, [])
    return total

def K_stirling(n):
    """(18): K_n = (-1)^n sum_{k=1}^{n+1} s(n+1,k) (k-1)!, signed Stirling row,
    from the falling factorial x(x-1)...(x-n)."""
    import sympy as sp
    x = sp.Symbol('x')
    expr = sp.prod(x - i for i in range(0, n + 1))  # x(x-1)...(x-n)
    coeff = sp.Poly(expr, x).all_coeffs()  # degree n+1 down to 0
    s = {}
    for idx, c in enumerate(coeff):
        power = len(coeff) - 1 - idx
        s[power] = int(c)
    return (-1) ** n * sum(s[k] * factorial(k - 1) for k in range(1, n + 2))

Kc = [K_composition(n) for n in range(0, 15)]
Ks = [K_stirling(n) for n in range(0, 15)]
out['B_composition_formula'] = Kc[:15]
out['B_stirling_formula'] = Ks[:15]
assert Kc == Ks, "composition vs Stirling mismatch"
# cross-check against recurrence u_n * n!
Kr = [int(u[n] * factorial(n)) for n in range(0, 15)]
assert Kc == Kr, f"recurrence K mismatch: {Kc} vs {Kr}"
out['B_all_three_routes_agree'] = True
# a_n from (21): a_n = (-1)^n (K_n - n K_{n-1})
a = [(-1) ** n * (Kc[n] - n * Kc[n - 1]) for n in range(1, 15)]
out['B_a11_a12'] = (a[10], a[11])
assert a[10] == 319296 and a[11] == -519312

# kappa check: kappa_{n+1} = (n+1) K_n, kappa_5 = 40 per source Example 6.3
kappa5 = 5 * Kc[4]
assert kappa5 == 40, f"kappa_5 = {kappa5} != 40 (source Example 6.3)"
out['B_kappa5_matches_source_example'] = kappa5

# ---------- C. numpy arrowhead eigen-decompositions ------------------
def arrowhead(N):
    t = np.arange(N) / N
    v = np.sqrt((1 - t) / N)
    H = np.zeros((N + 1, N + 1))
    H[0, 1:] = v
    H[1:, 0] = v
    H[1:, 1:] = np.diag(t)
    return H

def center_moments(N, nmax):
    H = arrowhead(N)
    Hp = np.eye(N + 1)
    mom = []
    for _ in range(nmax + 1):
        mom.append(Hp[0, 0])
        Hp = Hp @ H
    return mom

rows = []
for N in [16, 32, 64, 128, 256, 512, 1024]:
    H = arrowhead(N)
    ev, evec = np.linalg.eigh(H)
    lmin, lmax = ev.min(), ev.max()
    assert lmin >= -1 - 1e-9 and lmax <= 1 + 1e-9
    neg_ev = ev[ev < -1e-12]
    n_neg = len(neg_ev)
    # uniqueness: all negative eigenvalues equal (single eigenvalue, mult ok)
    uniq_neg = np.unique(np.round(neg_ev, 9)) if n_neg else []
    # restriction a=0 PSD: submatrix diag(t) PSD trivially (t>=0) - verify
    assert np.all(np.diag(H)[1:] >= 0)
    q = -neg_ev[0] if n_neg else None
    # center spectral moments
    mom = center_moments(N, 16)
    uN = mom
    bN = [uN[0]] + [uN[i] - uN[i - 1] for i in range(1, 17)]
    # second moment of center measure
    m2 = (H @ H)[0, 0]
    rows.append({
        'N': N,
        'lambda_min': float(lmin), 'lambda_max': float(lmax),
        'n_negative': int(n_neg),
        'negative_eigenvalues_unique': [float(x) for x in uniq_neg],
        'q': float(q) if q else None,
        'q_ge_half': bool(q >= 0.5 - 1e-9) if q else None,
        'second_moment': float(m2),
        'second_moment_formula_(N+1)/2N': float((N + 1) / (2 * N)),
        'b3': float(bN[3]), 'b12': float(bN[12]), 'b14': float(bN[14]),
        'b12_le_-1_2000': bool(bN[12] <= -1 / 2000 + 1e-15),
        'b14_le_b12': bool(bN[14] <= bN[12] + 1e-15),
        'mb3_ge_1_4': bool(-bN[3] >= 0.25 - 1e-12),
    })

out['C_eigh_rows'] = rows
for r in rows:
    assert r['n_negative'] == 1, f"N={r['N']}: {r['n_negative']} negative eigenvalues"
    assert r['q_ge_half']
    assert abs(r['second_moment'] - r['second_moment_formula_(N+1)/2N']) < 1e-12
    # criterion hypotheses engage only for large N (proof needs "sufficiently large")
    if r['N'] >= 128:
        assert r['b12_le_-1_2000'] and r['b14_le_b12'] and r['mb3_ge_1_4'], r
out['C_criterion_engages_from_N'] = 128
out['C_all_arrowhead_properties_hold'] = True

# ---------- D. Test the criterion's implied bounds on actual matrices
# even: b_{12+2m} <= -4^{-m}/2000 ; odd: b_{2m+1} <= -4^{-m}
viol = []
for N in [128, 256, 512]:
    mom = center_moments(N, 40)
    bN = [mom[0]] + [mom[i] - mom[i - 1] for i in range(1, 41)]
    for m in range(0, 15):
        if bN[12 + 2 * m] > -(4.0 ** -m) / 2000 + 1e-15:
            viol.append(('even', N, m, bN[12 + 2 * m]))
        if bN[2 * m + 1] > -(4.0 ** -m) + 1e-15:
            viol.append(('odd', N, m, bN[2 * m + 1]))
out['D_bound_violations'] = viol
assert not viol
out['D_implied_bounds_hold_on_actual_matrices'] = True

# ---------- E. limit argument sanity: b_n^(N) -> b_n ------------------
errs = {n: abs(rows[-1]['b3']) for n in [3]}
# compare b12^(512) to exact
b12_512 = [r for r in rows if r['N'] == 512][0]['b12']
out['E_b12_512_vs_exact'] = {'finite': b12_512, 'exact': float(b[12]),
                              'abs_err': abs(b12_512 - float(b[12]))}

with open('independent-check.json', 'w') as f:
    json.dump(out, f, indent=2, default=str)
print(json.dumps(out, indent=2, default=str)[:4000])
print("ALL INDEPENDENT CHECKS PASSED")

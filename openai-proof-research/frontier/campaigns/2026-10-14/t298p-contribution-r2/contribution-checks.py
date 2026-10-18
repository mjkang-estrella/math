#!/usr/bin/env python3
"""Independent finite contribution checks for T298P (review r2).

Pure standard library, exact rational arithmetic where possible, no network,
no writes except the JSON printed to stdout. These checks support attribution
and the operation-level comparison only. They prove no entropy, Fisher
information, tube-injectivity or microstate-recovery statement.

K1  normal-slice rank: real rank of H -> (i[H,D1], i[H,D2]) on Hermitian k x k
    is k^2-1 (scalar commutant), so the normal dimension is k^2+1, for
    path and star trees, k=2..6, exact over Q.
K2  C_D bookkeeping in the candidate's lower volume step: exact coefficients
    of log d, log k, log eps, chi(X), c and log c_D after normalization.
K3  unitary-group volume constant: (1/l^2) log Vol U(l) + (1/2) log l tends to
    3/4 + (1/2) log 2pi (the constant of NSS math/9809081v1 Lemma 2.8),
    using Vol U(l) = (2pi)^{l(l+1)/2} / prod_{j<l} j! (Vol U(1)=2pi).
K4  paid relative route versus the unconditional quantities: exact
    coefficients of log eps and log u0 in the excess chi(Z)-chi(Z|M_k)
    implied by the candidate formula (2) versus the relative entry value, and
    in the relative Fisher increment. Diagnostic of where the paid route
    diverges; conditional on the candidate formulas, not a proof.
"""
import json
import math
from fractions import Fraction as F


def cmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def cadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def matmul(A, B):
    n = len(A)
    Z = (F(0), F(0))
    out = [[Z] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = Z
            for l in range(n):
                s = cadd(s, cmul(A[i][l], B[l][j]))
            out[i][j] = s
    return out


def herm_basis(k):
    basis = []
    for j in range(k):
        M = [[(F(0), F(0))] * k for _ in range(k)]
        M[j][j] = (F(1), F(0))
        basis.append(M)
    for j in range(k):
        for l in range(j + 1, k):
            M = [[(F(0), F(0))] * k for _ in range(k)]
            M[j][l] = (F(1), F(0)); M[l][j] = (F(1), F(0))
            basis.append(M)
            M = [[(F(0), F(0))] * k for _ in range(k)]
            M[j][l] = (F(0), F(1)); M[l][j] = (F(0), F(-1))
            basis.append(M)
    return basis


def herm_coords(M):
    k = len(M)
    v = [M[j][j][0] for j in range(k)]
    for j in range(k):
        for l in range(j + 1, k):
            v.extend([M[j][l][0], M[j][l][1]])
    return v


def i_commutator(H, D):
    HD = matmul(H, D); DH = matmul(D, H)
    k = len(H)
    out = [[None] * k for _ in range(k)]
    for a in range(k):
        for b in range(k):
            d = (HD[a][b][0] - DH[a][b][0], HD[a][b][1] - DH[a][b][1])
            out[a][b] = (-d[1], d[0])  # multiply by i
    return out


def rank(rows):
    rows = [r[:] for r in rows]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def k1():
    out = []
    for k in range(2, 7):
        D1 = [[(F(i + 1) if i == j else F(0), F(0)) for j in range(k)] for i in range(k)]
        trees = {
            'path': [(i, i + 1) for i in range(k - 1)],
            'star': [(0, i) for i in range(1, k)],
        }
        for name, edges in trees.items():
            D2 = [[(F(0), F(0))] * k for _ in range(k)]
            for a, b in edges:
                D2[a][b] = (F(1), F(0)); D2[b][a] = (F(1), F(0))
            cols = []
            for H in herm_basis(k):
                cols.append(herm_coords(i_commutator(H, D1)) + herm_coords(i_commutator(H, D2)))
            rk = rank(cols)
            out.append({'k': k, 'tree': name, 'rank': rk, 'expected_rank': k * k - 1,
                        'normal_dim': 2 * k * k - rk, 'ok': rk == k * k - 1})
    return out


def k2():
    rows = []
    for k in range(1, 11):
        n = k * k + 1
        k2_ = F(k * k)
        # log d coefficients (divided by (kd)^2 = k^2 d^2), plus +1 from the
        # two-variable normalization log(kd).
        logd = (F(-(k * k - 1), 2) - F(n, 2)) / k2_ + 1
        # log k: orbit -(k^2+1)/2, fiber +n/2, then /k^2, plus +1 from log(kd).
        logk = (F(-(k * k + 1), 2) + F(n, 2)) / k2_ + 1
        rows.append({
            'k': k, 'n': n,
            'coef_log_d': str(logd), 'coef_log_k': str(logk),
            'coef_chi_source': str(F(1) / k2_),
            'coef_log_eps': str(F(n) / k2_),
            'coef_c': str(F(k * k - 1) / k2_),
            'coef_log_cD': str(F(1) / k2_),
            'ok': logd == 0 and logk == 1,
        })
    return rows


def log_vol_u(l):
    return (l * (l + 1) / 2) * math.log(2 * math.pi) - sum(math.lgamma(j + 1) for j in range(1, l))


def k3():
    target = 0.75 + 0.5 * math.log(2 * math.pi)
    vals = []
    for l in (10, 100, 1000, 10000, 100000):
        v = log_vol_u(l) / (l * l) + 0.5 * math.log(l)
        vals.append({'l': l, 'value': v, 'error': v - target})
    return {'target': target, 'vol_u1_is_2pi': abs(math.exp(log_vol_u(1)) - 2 * math.pi) < 1e-12,
            'values': vals, 'ok': abs(vals[-1]['error']) < 1e-6}


def k4():
    rows = []
    for k in range(2, 9):
        n = k * k + 1
        orb = k * k - 1
        # Unconditional chi(Z) by candidate (2): log eps coefficient n/k^2, no T term.
        # Relative chi(Z|M_k) from the 2k^2 entry coordinates eps*O(U,T):
        # log eps coefficient 2k^2/k^2 = 2, log u0 coefficient (k^2-1)/(2k^2).
        excess_log_eps = F(n, k * k) - 2
        excess_log_u0 = -F(orb, 2 * k * k)
        # Relative Fisher: Phi*(Z_t:M_k) = [Phi*(U)+(k^2-1)/u]/(eps^2 k^4),
        # dt = eps^2 k^2 du, chi* increment = (1/2) int Phi* dt.
        relative_orbital_increment_coef = F(orb, 2 * k * k)
        rows.append({
            'k': k,
            'micro_excess_coef_log_eps': str(excess_log_eps),
            'micro_excess_coef_log_u0': str(excess_log_u0),
            'micro_excess_equals_-(k2-1)/(2k2)*log(eps^2 u0)':
                excess_log_eps == 2 * excess_log_u0,
            'relative_fisher_orbital_increment_coef_of_log(U/u0)': str(relative_orbital_increment_coef),
            'paid_route_diverges_as_u0_to_0': relative_orbital_increment_coef > 0,
            'coefficients_match_in_magnitude': relative_orbital_increment_coef == -excess_log_u0,
        })
    return rows


def main():
    r1, r2, r3, r4 = k1(), k2(), k3(), k4()
    ok = all(x['ok'] for x in r1) and all(x['ok'] for x in r2) and r3['ok'] and r3['vol_u1_is_2pi'] \
        and all(x['paid_route_diverges_as_u0_to_0'] and x['coefficients_match_in_magnitude']
                and x['micro_excess_equals_-(k2-1)/(2k2)*log(eps^2 u0)'] for x in r4)
    print(json.dumps({'scope': 'finite attribution/normalization diagnostics only; no entropy theorem',
                      'K1_normal_slice_rank': r1, 'K2_CD_bookkeeping': r2,
                      'K3_unitary_volume_constant': r3, 'K4_paid_route_coefficients': r4,
                      'all_ok': ok}, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()

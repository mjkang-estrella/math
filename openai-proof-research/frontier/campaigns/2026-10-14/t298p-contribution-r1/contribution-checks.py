#!/usr/bin/env python3
"""T298P contribution review r1: attribution/normalization checks. Not a proof.

Pure standard library; writes JSON to stdout only. These finite computations
support the operation-level contribution comparison in review.md:
  C1 normal-slice count (exact rank over Q(i) for path trees, k=2..6);
  C2 Hermitian completeness identity behind the 2k^2/k semicircular coefficient
     normalization (exact, k=2..5) and the resulting relative-Fisher scale
     1/(eps^2 k^4), checked against the semicircular case;
  C3 the PAID relative route (NSS math/9809080v1 Prop. 4.1 + projection, and
     Shlyakhtenko math/9812079v1 Sec. 5) applied to the noisy encoding: its
     orbital term integrates to +infinity / -infinity as the noise time -> 0;
  C4 the orbit-volume constant c=3/4+(1/2)log(2pi) used by the candidate is the
     constant of NSS math/9809081v1 Lemma 2.8 for the unnormalized HS metric;
  C5 exact cancellation of the log d and log k coefficients in C_D.
"""
import json, math
from fractions import Fraction as F

# ---------- Gaussian-rational helpers: complex numbers as (re, im) Fractions
def cm(a, b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def ca(a, b): return (a[0]+b[0], a[1]+b[1])
Z0 = (F(0), F(0))

def matmul(A, B):
    k = len(A)
    return [[ (lambda i, j: _sum([cm(A[i][l], B[l][j]) for l in range(k)]))(i, j)
              for j in range(k)] for i in range(k)]
def _sum(xs):
    s = Z0
    for x in xs: s = ca(s, x)
    return s
def sub(A, B): return [[(A[i][j][0]-B[i][j][0], A[i][j][1]-B[i][j][1]) for j in range(len(A))] for i in range(len(A))]
def scal(c, A): return [[cm(c, x) for x in row] for row in A]

def herm_basis(k):
    """Real basis of Hermitian k x k matrices (not normalized)."""
    out = []
    for j in range(k):
        M = [[Z0]*k for _ in range(k)]; M[j][j] = (F(1), F(0)); out.append(M)
    for j in range(k):
        for l in range(j+1, k):
            M = [[Z0]*k for _ in range(k)]; M[j][l] = (F(1), F(0)); M[l][j] = (F(1), F(0)); out.append(M)
            M = [[Z0]*k for _ in range(k)]; M[j][l] = (F(0), F(1)); M[l][j] = (F(0), F(-1)); out.append(M)
    return out

def rank_Q(rows):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c] / rows[rk][c]
                rows[i] = [x - f*y for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def C1(kmax=6):
    res = {}
    I = (F(0), F(1))
    for k in range(2, kmax+1):
        D = [[(F(i+1) if i == j else F(0), F(0)) for j in range(k)] for i in range(k)]
        B = [[(F(1) if abs(i-j) == 1 else F(0), F(0)) for j in range(k)] for i in range(k)]  # path tree
        rows = []
        for H in herm_basis(k):
            img = []
            for Ds in (D, B):
                C = scal(I, sub(matmul(H, Ds), matmul(Ds, H)))   # i[H,D_s], Hermitian
                img += [x for row in C for z in row for x in z]
            rows.append(img)
        r = rank_Q(rows)
        res[k] = {"real_dim_Herm": k*k, "rank_L": r, "kernel_dim": k*k - r,
                  "normal_dim": 2*k*k - r, "expected_normal_dim_k2_plus_1": k*k + 1,
                  "ok": (k*k - r == 1 and 2*k*k - r == k*k + 1)}
    return res

def C2(kmax=5):
    """Sum_a (E_a)_ij (E_a)_lm = delta_im delta_jl for a Tr-orthonormal Hermitian basis.
    Off-diagonal basis elements carry 1/sqrt2, so products carry exactly 1/2."""
    res = {}
    for k in range(2, kmax+1):
        basis = herm_basis(k)
        weights = [F(1) if sum(1 for row in M for z in row if z != Z0) == 1 else F(1, 2) for M in basis]
        ok = True
        for i in range(k):
            for j in range(k):
                for l in range(k):
                    for m in range(k):
                        s = Z0
                        for w, M in zip(weights, basis):
                            s = ca(s, cm((w, F(0)), cm(M[i][j], M[l][m])))
                        want = (F(1) if (i == m and j == l) else F(0), F(0))
                        ok = ok and (s == want)
        # Variance of sum_a H_a (x) s_a with tr_k-orthonormal H_a = sqrt(k) E_a, 2 coordinates:
        # tau(x)tr_k((sum_a H_a s_a)^2) = (1/k) sum_a Tr(H_a^2) = (1/k) * k * k^2 = k^2 per coordinate.
        var_per_coord = F(1, k) * k * (k*k)
        # Relative-Fisher scale from the semicircular case: Z-D = eps*k*S_pair (2 vars),
        # Phi*(Z:M_k) = 2/(eps^2 k^2); Phi*(Y)=2k^2 for 2k^2 standard coefficients.
        ratio_times_eps2 = F(2, k*k) / F(2*k*k)
        res[k] = {"completeness_identity_exact": ok, "variance_per_coordinate": str(var_per_coord),
                  "Phi_rel_over_Phi_entries_times_eps2": str(ratio_times_eps2),
                  "equals_1_over_k4": ratio_times_eps2 == F(1, k**4)}
    return res

def C3():
    """Paid relative route on the noisy encoding Z_t = D + eps(V U(u) + O T(u)), t = eps^2 k^2 u.
    NSS Prop 4.1 + projection: Phi*(Z_t) <= [Phi*(U(u)) + (k^2-1)/u] / (eps^2 k^4).
    chi*-increment bound = (1/2) int Phi* dt = (1/(2k^2)) int_0^U0 [Phi*(U(u)) + (k^2-1)/u] du.
    Orbital part with lower limit u0: (k^2-1)/(2k^2) * log(U0/u0)."""
    out = {}
    for k in (2, 3, 2**32):
        kk = float(k)
        coef = (kk*kk - 1) / (2*kk*kk)
        out[str(k)] = {"orbital_fisher_increment_coefficient": coef,
                       "orbital_part_U0=1": {f"u0=1e-{e}": coef*math.log(10**e) for e in (2, 8, 32)},
                       "candidate_bound_(3)_orbital_part_order": "C eps^-1 (1+Phi*) integrated over dt=eps^2k^2 du gives O(eps)",
                       "shlyakhtenko_sec5_lower_orbital_term": "k^-2 * ((k^2-1)/2) * log(2 pi e u) -> -infinity as u->0"}
    return out

def C4(ls=(100, 1000, 10000, 100000)):
    """Vol U(l) in the unnormalized HS metric = (2pi)^{l(l+1)/2} / prod_{j=1}^{l-1} j!."""
    target = 0.75 + 0.5*math.log(2*math.pi)
    rows = {}
    for l in ls:
        logvol = (l*(l+1)/2)*math.log(2*math.pi) - sum(math.lgamma(j+1) for j in range(1, l))
        val = logvol/(l*l) + 0.5*math.log(l)
        rows[l] = {"logVol/l^2+log(l)/2": val, "minus_target": val - target}
    return {"target_3/4+log(2pi)/2": target, "rows": rows,
            "note": "NSS math/9809081v1 Lemma 2.8 (Killing form Re Tr(ab*), i.e. unnormalized HS) states this limit"}

def C5(kmax=10):
    """Coefficients (log d, log k) after normalization, from
    log A_d/d^2 = -(k^2-1)/2 log d -(k^2+1)/2 log k + ..., fiber (n/2) log k, source -(n/2) log d,
    divide by k^2 and add output 2-variable normalization log(kd)."""
    res = {}
    for k in range(1, kmax+1):
        n = k*k + 1
        logd = (F(-(k*k-1), 2) + F(-n, 2)) / (k*k) + 1
        logk = (F(-(k*k+1), 2) + F(n, 2)) / (k*k) + 1
        res[k] = {"log_d_coeff": str(logd), "log_k_coeff": str(logk), "ok": logd == 0 and logk == 1}
    return res

if __name__ == "__main__":
    out = {"C1_normal_slice": C1(), "C2_coefficient_normalization": C2(), "C3_paid_route_divergence": C3(),
           "C4_unitary_volume_constant": C4(), "C5_CD_exponent_cancellation": C5(),
           "scope": "finite attribution/normalization checks only; no entropy, Fisher or free-probability theorem is proved"}
    out["all_exact_ok"] = (all(v["ok"] for v in out["C1_normal_slice"].values())
                           and all(v["completeness_identity_exact"] and v["equals_1_over_k4"] for v in out["C2_coefficient_normalization"].values())
                           and all(v["ok"] for v in out["C5_CD_exponent_cancellation"].values()))
    print(json.dumps(out, indent=1, sort_keys=True, default=str))

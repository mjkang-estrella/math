"""Re-derivation diagnostics for the matched volume constants (candidate Sec. 2).

1. log Vol U(l) (unnormalized HS metric) from the first-column recursion equals
   (l(l+1)/2) log 2pi - sum_{j<l} log j!, and (log Vol U(l) + l^2 log(l)/2)/l^2 -> c.
2. c_D and the amplified orbit spectrum (each scalar singular value d^2 times),
   stabilizer metric factor k, normal-fibre factor sqrt(k).
3. Exact log A_d versus the asymptotic formula.
4. Lower-bound normalization -> k^-2 chi + (n/k^2) log eps + C_D.
5. Upper-bound accounting with rank loss l=N-kd: no residual log N term and an
   error that vanishes as theta -> 0 (net cost theta log(C/eta) kept explicit).
Numerical diagnostics only.
"""
import json, sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import slice_bases, herm_basis

c_const = 0.75 + 0.5 * math.log(2 * math.pi)

def logvolU(l):
    return l * (l + 1) / 2 * math.log(2 * math.pi) - sum(math.lgamma(j + 1) for j in range(1, l))

def logvolU_recursion(l):
    # Vol U(1)=2pi; Vol U(l)=Vol U(l-1) * 2^(l-1) * area(S^(2l-1)), area=2 pi^l/(l-1)!
    v = math.log(2 * math.pi)
    for j in range(2, l + 1):
        v += (j - 1) * math.log(2) + math.log(2) + j * math.log(math.pi) - math.lgamma(j)
    return v

out = {"c": c_const}
out["recursion_vs_product_max_err"] = max(abs(logvolU(l) - logvolU_recursion(l)) for l in range(1, 60))
out["c_convergence"] = {str(l): (logvolU(l) + l * l * math.log(l) / 2) / l**2 for l in [100, 1000, 10000]}

res = []
for k in [2, 3, 4]:
    (D1, B), V, O, L, s, traceless, _ = slice_bases(k, "path")
    sv = s[s > 1e-10]
    log_cD = float(np.sum(np.log(sv)))
    n = k * k + 1
    amp_err = 0.0
    for d in [1, 2, 3]:
        Hk = herm_basis(k)
        Hd = [h / math.sqrt(d) for h in herm_basis(d)]  # orthonormal for Tr_d
        # basis of M_kd^sa orthonormal for Tr_kd: (h (x) g)/sqrt(k)
        basis = [np.kron(h, g) / math.sqrt(k) for h in Hk for g in Hd]
        Dk = [np.kron(D1, np.eye(d)), np.kron(B, np.eye(d))]
        Hkd = herm_basis(k * d)
        Hkd = [h / math.sqrt(k * d) for h in Hkd]  # Tr_kd orthonormal
        cols = []
        for K in basis:
            img = [1j * (K @ Dt - Dt @ K) for Dt in Dk]
            cols.append(np.concatenate([[np.trace(h @ im).real for h in Hkd] for im in img]))
        M = np.array(cols).T
        s_amp = np.linalg.svd(M, compute_uv=False)
        s_amp = np.sort(s_amp[s_amp > 1e-9])
        target = np.sort(np.repeat(sv, d * d))
        assert len(s_amp) == (k * k - 1) * d * d
        amp_err = max(amp_err, float(np.abs(s_amp - target).max()))
        # stabilizer: I_k (x) g has Tr_kd squared norm k * Tr_d(g^2)
        g = Hd[0]
        stab = np.trace(np.kron(np.eye(k), g) @ np.kron(np.eye(k), g)).real
        assert abs(stab - k) < 1e-12
        # normal fibre: sum_s Tr_kd((V_as (x) g)^2) = k
        fib = sum(np.trace(np.kron(V[0][t], g) @ np.kron(V[0][t], g)).real for t in range(2))
        assert abs(fib - k) < 1e-12
    # exact log A_d vs asymptotic
    asym = []
    for d in [50, 500, 2000]:
        exact = d * d * log_cD + logvolU(k * d) - d * d / 2 * math.log(k) - logvolU(d)
        formula = d * d * (-(k * k - 1) / 2 * math.log(d) - (k * k + 1) / 2 * math.log(k) + (k * k - 1) * c_const + log_cD)
        asym.append((d, (exact - formula) / d**2))
    C_D = math.log(k) + (k * k - 1) / k**2 * c_const + log_cD / k**2
    # lower-bound normalization with chi(A)=chiA, eps
    chiA, eps = -1.7, 0.01
    low = []
    for d in [50, 500, 2000]:
        logA = d * d * log_cD + logvolU(k * d) - d * d / 2 * math.log(k) - logvolU(d)
        total = (logA + n * d * d * math.log(eps * math.sqrt(k)) + d * d * (chiA - n / 2 * math.log(d))) / (k * d) ** 2 + math.log(k * d)
        low.append((d, total - (chiA / k**2 + n / k**2 * math.log(eps) + C_D)))
    # upper-bound accounting: N arbitrary, r = k d', l = N - r ~ theta N
    R, logCeta = 3.0, math.log(10.0)
    up = {}
    for theta in [0.1, 0.03, 0.01]:
        vals = []
        for N in [2001, 20001, 200001]:
            dprime = int((1 - theta) * N / k)
            r = k * dprime
            Mdim = 2 * (N * N - r * r)
            rad = math.sqrt(2 * N) * R
            logball = Mdim / 2 * math.log(math.pi) + Mdim * math.log(rad) - math.lgamma(Mdim / 2 + 1)
            # tube part via the asymptotic formula (exact lgamma sums too slow for huge d')
            logA = dprime**2 * (-(k * k - 1) / 2 * math.log(dprime) - (k * k + 1) / 2 * math.log(k) + (k * k - 1) * c_const + log_cD)
            tube = logA + n * dprime**2 * math.log(eps * math.sqrt(k)) + dprime**2 * (chiA - n / 2 * math.log(dprime))
            net = 2 * N * (N - r) * logCeta + math.log(N + 1)
            total = (tube + logball + net) / N**2 + math.log(N)
            vals.append(total - (chiA / k**2 + n / k**2 * math.log(eps) + C_D))
        up[str(theta)] = vals
    res.append(dict(k=k, log_cD=log_cD, C_D=C_D, amplified_singular_err=amp_err,
                    logA_asym_err_per_d2=asym, lower_norm_err=low, upper_excess_by_theta=up))
    assert amp_err < 1e-9
    assert abs(asym[-1][1]) < 0.01 and abs(low[-1][1]) < 0.01
    for th, v in up.items():
        assert abs(v[-1] - v[-2]) < 0.01  # no log N drift
out["per_k"] = res
assert out["recursion_vs_product_max_err"] < 1e-8
print(json.dumps(out, indent=1))

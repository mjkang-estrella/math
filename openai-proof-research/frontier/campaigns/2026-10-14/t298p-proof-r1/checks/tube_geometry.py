"""Tube-geometry diagnostics (candidate Sec. 1, matched-volume A/F).

(a) uniform local normal solver: fixed-point K <- K + L^{-1} G(K,W) on the orbit
    complement, G = P_o(exp(-iK)(D+W)exp(iK) - D); iteration counts and the
    normal remainder ||Y - P_v W|| / ||W||^2 versus matrix size d.
(b) bundle Jacobian at normal displacement Y relative to Y=0 (horizontal +
    normal block, plus stabilizer-fibre factor): |log ratio| / (||Y|| d^2).
(c) almost-commuting step of the global-uniqueness argument: for W near and far
    from the stabilizer, dist(W, I(x)U(d)) via averaged diagonal block + polar
    part, divided by max_s ||[W, D_s (x) I]||.
Floating diagnostics only.
"""
import json, sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import slice_bases, herm_basis

rng = np.random.default_rng(4242)

def expi(K):
    w, Q = np.linalg.eigh(K)
    return (Q * np.exp(1j * w)) @ Q.conj().T

def opn(x):
    return np.linalg.norm(x, 2)

def polar(x):
    u, s, vh = np.linalg.svd(x)
    return u @ vh

def setup(k):
    (D1, B), V, O, L, s, traceless, pair_basis = slice_bases(k, "path")
    Hk = herm_basis(k)
    # real 2k^2 x 2k^2 matrix: columns = coefficient vectors of [L(traceless_beta) | V_a]
    def pair_coords(p):
        return np.array([np.trace(pb[0] @ p[0] + pb[1] @ p[1]).real / k for pb in pair_basis])
    Lcols = [pair_coords((1j * (h @ D1 - D1 @ h), 1j * (h @ B - B @ h))) for h in traceless]
    Vcols = [pair_coords(v) for v in V]
    M = np.column_stack(Lcols + Vcols)
    Minv = np.linalg.inv(M)
    return (D1, B), V, traceless, pair_basis, Minv

def decompose(P, k, d, traceless, pair_basis, Minv):
    """P = i[K,D(x)I] + Y with K in orbit complement, Y normal. Coefficientwise."""
    # coefficient d x d blocks of P along pair_basis
    coeffs = []
    for pb in pair_basis:
        c = 0
        for t in range(2):
            if np.abs(pb[t]).max() > 0:
                X = np.kron(pb[t], np.eye(d)) @ P[t]
                c = c + sum(X[i * d:(i + 1) * d, i * d:(i + 1) * d] for i in range(k)) / k
        coeffs.append(c)
    coeffs = np.array(coeffs)  # (2k^2, d, d)
    sol = np.einsum('ab,bij->aij', Minv, coeffs)
    nk = len(traceless)
    K = sum(np.kron(traceless[b], sol[b]) for b in range(nk))
    ycoef = sol[nk:]
    return K, ycoef

res_a, res_b, res_c = [], [], []
for k in [2, 3]:
    (D1, B), V, traceless, pair_basis, Minv = setup(k)
    n = len(V)
    for d in [1, 2, 4, 6]:
        Dk = [np.kron(D1, np.eye(d)), np.kron(B, np.eye(d))]
        # (a) local solver
        for rho in [0.02, 0.05]:
            def rh():
                x = rng.normal(size=(k * d, k * d)) + 1j * rng.normal(size=(k * d, k * d))
                x = (x + x.conj().T) / 2
                return x / opn(x)
            W = [rho * rh(), rho * rh()]
            K = np.zeros((k * d, k * d), dtype=complex)
            it = 0
            for it in range(1, 200):
                U = expi(K)
                C = [U.conj().T @ (Dk[t] + W[t]) @ U - Dk[t] for t in range(2)]
                dK, _ = decompose(C, k, d, traceless, pair_basis, Minv)
                # G(K,W) = P_o(C); P_o C = i[dK', D]; update K <- K - dK (sign: C ~ W - i[K,D])
                K = K + dK
                if opn(dK) < 1e-13:
                    break
            U = expi(K)
            C = [U.conj().T @ (Dk[t] + W[t]) @ U - Dk[t] for t in range(2)]
            Kres, ycoef = decompose(C, k, d, traceless, pair_basis, Minv)
            _, yW = decompose(W, k, d, traceless, pair_basis, Minv)
            yrem = max(opn(ycoef[a] - yW[a]) for a in range(n))
            res_a.append(dict(k=k, d=d, rho=rho, iterations=it, orbit_residual=float(opn(Kres)),
                              K_norm_over_rho=float(opn(K) / rho), normal_remainder_over_rho2=float(yrem / rho**2)))
        # (b) Jacobian ratio
        Hkd = [h / math.sqrt(k * d) for h in herm_basis(k * d)]
        Hd = [h / math.sqrt(d) for h in herm_basis(d)]
        Hk = herm_basis(k)
        horiz = [np.kron(h, g) / math.sqrt(k) for h in traceless for g in Hd]
        stabd = [np.kron(np.eye(k), g) / math.sqrt(k) for g in Hd]
        normal = [(np.kron(V[a][0], g) / math.sqrt(k), np.kron(V[a][1], g) / math.sqrt(k)) for a in range(n) for g in Hd]
        def vec(p):
            return np.concatenate([[np.trace(h @ p[t]).real for h in Hkd] for t in range(2)])
        def jac(Y):
            Dy = [Dk[t] + Y[t] for t in range(2)]
            cols = [vec([1j * (K @ Dy[t] - Dy[t] @ K) for t in range(2)]) for K in horiz + stabd]
            cols += [vec(p) for p in normal]
            M = np.array(cols).T
            # coarea Jacobian of full differential, divided by stabilizer-fibre volume factor
            full = np.linalg.slogdet(M @ M.T)[1] / 2
            # fibre tangent in U(kd) x normal: (iK_stab, -[K_stab, Y]) -> norm^2 1 + ||[K,Y]||^2
            fib = []
            for Ks in stabd:
                fib.append(np.concatenate([np.zeros(len(horiz)), [1.0 if Ks is s2 else 0.0 for s2 in stabd],
                                           [np.trace((np.kron(V[a][0], g) @ (1j * (Ks @ Y[0] - Y[0] @ Ks))) + np.kron(V[a][1], g) @ (1j * (Ks @ Y[1] - Y[1] @ Ks))).real / math.sqrt(k) for a in range(n) for g in Hd]]))
            F = np.array(fib)
            fibvol = np.linalg.slogdet(F @ F.T)[1] / 2
            return full - fibvol
        j0 = jac([0 * Dk[0], 0 * Dk[1]])
        for rho in [0.01, 0.03]:
            y = rng.normal(size=(n, d, d)) + 1j * rng.normal(size=(n, d, d))
            y = (y + np.conj(np.transpose(y, (0, 2, 1)))) / 2
            Y = [sum(np.kron(V[a][t], y[a]) for a in range(n)) for t in range(2)]
            sc = rho / max(opn(Y[0]), opn(Y[1]))
            Y = [sc * Y[0], sc * Y[1]]
            res_b.append(dict(k=k, d=d, rho=rho, log_jac_ratio=float(jac(Y) - j0),
                              ratio_over_rho_d2=float(abs(jac(Y) - j0) / (rho * d * d))))
        # (c) almost-commuting lemma
        worst = 0.0
        for scale in [1e-3, 1e-2, 0.1, 0.5, None]:
            for _ in range(5):
                if scale is None:
                    Z = rng.normal(size=(k * d, k * d)) + 1j * rng.normal(size=(k * d, k * d))
                    Wu, _ = np.linalg.qr(Z)
                else:
                    Kh = rng.normal(size=(k * d, k * d)) + 1j * rng.normal(size=(k * d, k * d))
                    Kh = (Kh + Kh.conj().T) / 2
                    g = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                    g, _ = np.linalg.qr(g)
                    Wu = expi(scale * Kh / opn(Kh)) @ np.kron(np.eye(k), g)
                comm = max(opn(Wu @ Dt - Dt @ Wu) for Dt in Dk)
                avg = sum(Wu[i * d:(i + 1) * d, i * d:(i + 1) * d] for i in range(k)) / k
                Vp = polar(avg)
                dist = opn(Wu - np.kron(np.eye(k), Vp))
                worst = max(worst, dist / comm)
        res_c.append(dict(k=k, d=d, max_dist_over_comm=float(worst)))

print(json.dumps(dict(local_solver=res_a, jacobian=res_b, almost_commuting=res_c), indent=1))
for r in res_a:
    assert r['orbit_residual'] < 1e-10 and r['iterations'] < 60

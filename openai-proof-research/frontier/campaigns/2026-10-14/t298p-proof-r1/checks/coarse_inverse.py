"""Re-derivation diagnostics for the coarse normal/inner inverse (candidate Sec. 3).

Coarse bimodule M_k (x) M_k with left action on the first factor and right
action on the second; inner product <x(x)y, x'(x)y'> = tr(x*x') tr(y*y').
Checks: normal-slice dimension, Gram 1/k, J* W = 0, rank J, kernel = span w_bc,
invertibility of F0 = [W-map | J on ker(J)^perp], the leading coefficient
(1/k)(V_aj)_{cb}, matrix-unit trace contraction for the entry adjoint, and
sum_j ||sum_a V_aj (x) xi_a||^2 = sum_a ||xi_a||^2 with random finite xi.
Floating diagnostics only; they do not prove any free-probability statement.
"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import E, slice_bases, tr

rng = np.random.default_rng(298)
out = []
for k in [2, 3, 4]:
    for tree in ["path", "star"]:
        if k == 2 and tree == "star":
            continue
        (D1, B), V, O, L, s, _, _ = slice_bases(k, tree)
        Ds = [D1, B]
        n = len(V)
        assert n == k * k + 1 and len(O) == k * k - 1
        # normal-space characterization sum_s [D_s, V_as] = 0
        char_err = max(np.abs(sum(Ds[t] @ v[t] - v[t] @ Ds[t] for t in range(2))).max() for v in V)
        # orthonormality of V for sum_s tr_k
        G = np.array([[sum(tr(V[a][t].conj().T @ V[b][t]) for t in range(2)).real for b in range(n)] for a in range(n)])
        orth_err = np.abs(G - np.eye(n)).max()
        # coarse space: 4-index tensors eta[i,j,l,m] <-> E_ij (x) E_lm
        def left(D, eta):
            return np.einsum('ip,pjlm->ijlm', D, eta)
        def right(eta, D):
            return np.einsum('ijlp,pm->ijlm', eta, D)
        def w(b, c):
            t = np.zeros((k, k, k, k), dtype=complex)
            for i in range(k):
                t[i, b, c, i] = 1.0
            return t
        ip = lambda x, y: np.vdot(x, y) / k**2
        W = []
        idx = []
        for a in range(n):
            for b in range(k):
                for c in range(k):
                    W.append(np.stack([left(V[a][t], w(b, c)) for t in range(2)]))
                    idx.append((a, b, c))
        Wm = np.array([x.reshape(-1) for x in W]).T / k  # columns, scaled so Euclid ip/k^2 -> plain
        gram = Wm.conj().T @ Wm
        gram_err = np.abs(gram - np.eye(len(W)) / k).max()
        # J on full coarse space
        dim = k**4
        Jcols = []
        for q in range(dim):
            e = np.zeros(dim, dtype=complex); e[q] = 1.0
            eta = e.reshape(k, k, k, k)
            Jcols.append(np.concatenate([(left(Ds[t], eta) - right(eta, Ds[t])).reshape(-1) for t in range(2)]))
        J = np.array(Jcols).T / k  # same normalization as Wm (domain ip also /k^2 -> factor cancels)
        rankJ = np.linalg.matrix_rank(J, tol=1e-9)
        JstarW = np.abs(J.conj().T @ Wm).max()
        # kernel of J equals span of w_bc
        wvecs = np.array([w(b, c).reshape(-1) for b in range(k) for c in range(k)]).T
        ker_err = np.abs(J @ wvecs).max()
        # F0 on (normal coefficients) + (eta in ker(J)^perp)
        qk, _ = np.linalg.qr(wvecs)
        P_perp = np.eye(dim) - qk @ qk.conj().T
        uu, ss, _ = np.linalg.svd(P_perp)
        comp = uu[:, :dim - k * k]
        F0 = np.column_stack([Wm, J @ comp])
        sv = np.linalg.svd(F0, compute_uv=False)
        # leading coefficient for target (delta_js 1(x)1)_s
        one = np.zeros((k, k, k, k), dtype=complex)
        for i in range(k):
            for l in range(k):
                one[i, i, l, l] = 1.0
        lead_err = 0.0
        eta_norm = 0.0
        for j in range(2):
            target = np.concatenate([(one if t == j else 0 * one).reshape(-1) for t in range(2)]) / k
            sol = np.linalg.solve(F0, target) if F0.shape[0] == F0.shape[1] else np.linalg.lstsq(F0, target, rcond=None)[0]
            theta = sol[:len(W)]
            pred = np.array([V[a][j][c, b] / k for (a, b, c) in idx])
            lead_err = max(lead_err, np.abs(theta - pred).max())
            resid = np.abs(F0 @ sol - target).max()
            assert resid < 1e-10
            eta_norm = max(eta_norm, float(np.linalg.norm(sol[len(W):])))
        # matrix-unit contraction: (tr(x)tr)[E_ij * Delta_{bc}] vs tr_k(E_cb E_ij)/k
        contr_err = 0.0
        for i in range(k):
            for j in range(k):
                for b in range(k):
                    for c in range(k):
                        val = sum(tr(E(k, i, j) @ E(k, l, b)) * tr(E(k, c, l)) for l in range(k))
                        # Delta(E_ij (x) p) = (E_ib (x) p1) (x) (E_cj (x) p2): trace part tr(E_ib)tr(E_cj)
                        lhs = tr(E(k, i, b)) * tr(E(k, c, j))
                        rhs = tr(E(k, c, b) @ E(k, i, j)) / k
                        contr_err = max(contr_err, abs(lhs - rhs), abs(val - lhs))
        # leading score norm identity with random finite "xi" (any Hilbert vectors)
        m = 5
        xi = [rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m)) for _ in range(n)]
        xi = [(x + x.conj().T) / 2 for x in xi]
        lhs = sum(np.real(tr((sum(np.kron(V[a][j], xi[a]) for a in range(n))).conj().T @ (sum(np.kron(V[a][j], xi[a]) for a in range(n))))) for j in range(2))
        rhs = sum(np.real(tr(x @ x)) for x in xi)
        out.append(dict(k=k, tree=tree, n=n, orbit_rank=int(np.sum(s > 1e-10)),
                        normal_char_err=float(char_err), V_orth_err=float(orth_err),
                        W_gram_err=float(gram_err), rank_J=int(rankJ), expected_rank_J=k**4 - k**2,
                        Jstar_W=float(JstarW), kernel_J_err=float(ker_err),
                        F0_shape=list(F0.shape), F0_min_sv=float(sv.min()), F0_max_sv=float(sv.max()),
                        leading_coeff_err=float(lead_err), inner_eta_norm=float(eta_norm),
                        matrix_unit_contraction_err=float(contr_err),
                        leading_score_norm_identity_err=float(abs(lhs - rhs) / rhs)))
        assert gram_err < 1e-12 and JstarW < 1e-12 and rankJ == k**4 - k**2 and ker_err < 1e-12
        assert F0.shape[0] == F0.shape[1] == 2 * k**4 and sv.min() > 1e-6
        assert lead_err < 1e-10 and contr_err < 1e-14 and abs(lhs - rhs) / rhs < 1e-12
        assert char_err < 1e-10 and orth_err < 1e-10
print(json.dumps(out, indent=1))

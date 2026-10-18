#!/usr/bin/env python3
"""Finite floating diagnostics for T298P proof review r2 (independent code).

Sections:
 1. coarse inverse: normal Gram 1/k, J*W=0, kernel of J = span w_bc,
    invertibility of L0, leading coefficient (V_aj)_cb / k;
 2. free-noise coefficient normalization: (1/k^2) sum_r B_rs (x) B_rs'
    reproduces delta_ss' times the standard GUE/semicircular covariance;
 3. almost-commutation: ||[W,D_s]||<=r forces dist(W, I_k (x) U(d)) <= C r;
 4. arbitrary-size recovery: a size-N matrix pair (N not a multiple of k)
    built from an encoded model plus junk rows and a large low-rank
    perturbation, conjugated by Haar unitary; band projections, truncated
    polar tree maps, root intersection, second Re/Im truncation, then the
    normal-tube solver; reports rank loss, operator distance to D and
    recovered moments;
 5. unitary-volume asymptotics used in A_d.
They support, but do not replace, the general arguments in review.md.
"""
import json, math
import numpy as np

rng = np.random.default_rng(29802)


def E(k, i, j):
    m = np.zeros((k, k), complex); m[i, j] = 1; return m


def tr(a):
    return np.trace(a) / a.shape[0]


def setup(k):
    D1 = np.diag(np.arange(1, k + 1)).astype(complex)
    D2 = np.zeros((k, k), complex)
    edges = [(i, i + 1) for i in range(k - 1)]
    for i, j in edges:
        D2[i, j] = D2[j, i] = 1
    H = []
    for i in range(k):
        H.append(np.sqrt(k) * E(k, i, i))
    for i in range(k):
        for j in range(i + 1, k):
            H.append(np.sqrt(k / 2) * (E(k, i, j) + E(k, j, i)))
            H.append(1j * np.sqrt(k / 2) * (E(k, i, j) - E(k, j, i)))
    pb = [(h, 0 * h) for h in H] + [(0 * h, h) for h in H]
    def coords(p):
        return np.array([tr(b[0].conj().T @ p[0] + b[1].conj().T @ p[1]).real for b in pb])
    L = np.column_stack([coords((1j * (h @ D1 - D1 @ h), 1j * (h @ D2 - D2 @ h))) for h in H])
    u, s, vt = np.linalg.svd(L)
    r = int((s > 1e-9).sum())
    def topair(c):
        return (sum(c[i] * pb[i][0] for i in range(len(pb))), sum(c[i] * pb[i][1] for i in range(len(pb))))
    V = [topair(u[:, a]) for a in range(r, 2 * k * k)]
    O = [topair(u[:, b]) for b in range(r)]
    return (D1, D2), V, O, H, pb, L, s[:r], edges


# ---------------- 1. coarse inverse ----------------
def coarse(k):
    Ds, V, O, H, pb, L, sv, _ = setup(k)
    n = len(V)
    left = lambda A, t: np.einsum('ip,pjlm->ijlm', A, t)
    right = lambda t, A: np.einsum('ijlp,pm->ijlm', t, A)
    def w(b, c):
        t = np.zeros((k,) * 4, complex)
        for i in range(k):
            t[i, b, c, i] = 1
        return t
    ip = lambda x, y: np.vdot(x, y) / k**2
    W = [np.stack([left(V[a][s], w(b, c)) for s in range(2)]) for a in range(n) for b in range(k) for c in range(k)]
    Wm = np.array([x.reshape(-1) for x in W]).T / k
    gram_err = np.abs(Wm.conj().T @ Wm - np.eye(Wm.shape[1]) / k).max()
    dim = k**4
    J = np.array([np.concatenate([(left(Ds[s], e.reshape((k,) * 4)) - right(e.reshape((k,) * 4), Ds[s])).reshape(-1) for s in range(2)])
                  for e in np.eye(dim, dtype=complex)]).T / k
    rankJ = np.linalg.matrix_rank(J, tol=1e-9)
    JW = np.abs(J.conj().T @ Wm).max()
    wv = np.array([w(b, c).reshape(-1) for b in range(k) for c in range(k)]).T
    kerr = np.abs(J @ wv).max()
    qk, _ = np.linalg.qr(wv)
    uu, _, _ = np.linalg.svd(np.eye(dim) - qk @ qk.conj().T)
    F0 = np.column_stack([Wm, J @ uu[:, :dim - k * k]])
    s0 = np.linalg.svd(F0, compute_uv=False)
    one = np.zeros((k,) * 4, complex)
    for i in range(k):
        for l in range(k):
            one[i, i, l, l] = 1
    lead = 0.0
    for j in range(2):
        tgt = np.concatenate([(one if s == j else 0 * one).reshape(-1) for s in range(2)]) / k
        coef = k * (Wm.conj().T @ tgt)   # projection coefficients on W (norm^2 = 1/k)
        pred = np.array([V[a][j][c, b] / k for a in range(n) for b in range(k) for c in range(k)])
        lead = max(lead, np.abs(coef - pred).max())
    return dict(k=k, n=n, gram_err=float(gram_err), rankJ=int(rankJ), rankJ_expected=k**4 - k**2,
                JstarW=float(JW), kernel_err=float(kerr), F0_min_sv=float(s0.min()), F0_shape=list(F0.shape),
                leading_coeff_err=float(lead))


# ---------------- 2. noise covariance ----------------
def noise(k):
    Ds, V, O, *_ = setup(k)
    B = V + O
    err = 0.0
    for s in range(2):
        for s2 in range(2):
            C = sum(np.einsum('ij,lm->ijlm', b[s], b[s2]) for b in B) / k**2
            T = np.zeros((k,) * 4, complex)
            if s == s2:
                for i in range(k):
                    for j in range(k):
                        T[i, j, j, i] = 1 / k
            err = max(err, np.abs(C - T).max())
    return dict(k=k, basis_size=len(B), covariance_err=float(err))


# ---------------- 3. almost commutation ----------------
def expmh(Hm):
    w, U = np.linalg.eigh(Hm)
    return (U * np.exp(1j * w)) @ U.conj().T


def polar_u(A):
    u, s, vh = np.linalg.svd(A)
    return u @ vh


def almost_commute(k, d=6, trials=40):
    Ds, *_ = setup(k)
    worst = 0.0
    for _ in range(trials):
        G = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
        w = polar_u(G)
        X = rng.normal(size=(k * d, k * d)) + 1j * rng.normal(size=(k * d, k * d))
        X = (X + X.conj().T) / 2
        X /= np.linalg.norm(X, 2)
        r = 10 ** rng.uniform(-4, -1.5)
        W = expmh(r * X) @ np.kron(np.eye(k), w)
        comm = max(np.linalg.norm(W @ np.kron(Ds[s], np.eye(d)) - np.kron(Ds[s], np.eye(d)) @ W, 2) for s in range(2))
        blocks = [W[i * d:(i + 1) * d, i * d:(i + 1) * d] for i in range(k)]
        v = polar_u(sum(blocks) / k)
        dist = np.linalg.norm(W - np.kron(np.eye(k), v), 2)
        worst = max(worst, dist / comm)
    return dict(k=k, d=d, max_dist_over_commutator=float(worst))


# ---------------- 4. arbitrary-size recovery ----------------
def herm_coeffs(A, k, d, H):
    """coefficients c_h in M_d with A = sum_h h (x) c_h  (H orthonormal for tr_k)."""
    A4 = A.reshape(k, d, k, d)
    return [np.einsum('ij,iajb->ab', h.conj(), A4) / k for h in H]


def solve_tube(Wp, k, d, Ds, V, O, H, pb, L, iters=40):
    """Solve Wp = exp(iK)(D(x)1 + Y)exp(-iK) for K in orbit coefficients (traceless), Y normal."""
    Dk = [np.kron(Ds[s], np.eye(d)) for s in range(2)]
    nb = len(pb)
    Lp = np.linalg.pinv(L)  # maps pair coords -> Hermitian coords of H (kernel = identity direction)
    K = np.zeros((k * d, k * d), complex)
    for _ in range(iters):
        U = expmh(K)
        R = [U.conj().T @ Wp[s] @ U - Dk[s] for s in range(2)]
        # pair-basis coefficients (each in M_d^sa)
        c = [herm_coeffs(R[0], k, d, H), herm_coeffs(R[1], k, d, H)]
        pc = [c[0][i] for i in range(k * k)] + [c[1][i] for i in range(k * k)]
        # orbit component: project onto range(L) coordinatewise, solve L x = proj
        Pc = np.array(pc)  # nb x d x d
        orbit_part = np.tensordot(L @ Lp, Pc, axes=(1, 0))
        res = float(max(np.abs(o).max() for o in orbit_part))
        if res < 1e-12:
            break
        hc = np.tensordot(Lp, Pc, axes=(1, 0))  # Hermitian coords of i[h,D] preimage
        dK = sum(np.kron(H[a], hc[a]) for a in range(k * k))
        # exp(-i dK)(D+R)exp(i dK) = D + R - i[dK,D] + O(|dK|^2); L(h)=i[h,D], so dK=L^+ P_o R.
        K = K + dK  # first-order update; iteration absorbs the composition error
        K = (K + K.conj().T) / 2
    U = expmh(K)
    R = [U.conj().T @ Wp[s] @ U - Dk[s] for s in range(2)]
    c = herm_coeffs(R[0], k, d, H) + herm_coeffs(R[1], k, d, H)
    Pc = np.array(c)
    # normal coefficients: V_a coordinates
    Vc = []
    for a in range(len(V)):
        va = np.array([tr(b[0].conj().T @ V[a][0] + b[1].conj().T @ V[a][1]).real for b in pb])
        Vc.append(np.tensordot(va, Pc, axes=(0, 0)))
    return Vc, res


def subspace_intersect(Bs, P):
    """Orthonormal basis (in coordinates of columns of Bs) of {x : (1-P) Bs x = 0}."""
    M = (np.eye(P.shape[0]) - P) @ Bs
    u, s, vh = np.linalg.svd(M, full_matrices=True)
    null = vh[(s > 1e-8).sum():].conj().T
    return null


def recovery(k=3, d=36, extra=5, junk_rank=3, eps=0.02, seed=1):
    r = np.random.default_rng(seed)
    Ds, V, O, H, pb, L, sv, edges = setup(k)
    n = len(V)
    x = []
    for a in range(n):
        G = r.normal(size=(d, d)) + 1j * r.normal(size=(d, d))
        G = (G + G.conj().T) / (2 * np.sqrt(2 * d))
        x.append(G + 0.3 * np.diag(np.sign(r.normal(size=d))))  # non-semicircular perturbation
    Z0 = [np.kron(Ds[s], np.eye(d)) + eps * sum(np.kron(V[a][s], x[a]) for a in range(n)) for s in range(2)]
    # actual-model entry bound a: max Re/Im norm of the encoded deviations, with slack 1.5
    a_entry = 0.0
    for s in range(2):
        for i in range(k):
            for j in range(k):
                Bk = Z0[s][i * d:(i + 1) * d, j * d:(j + 1) * d] - Ds[s][i, j] * np.eye(d)
                for Hm in [(Bk + Bk.conj().T) / 2, (Bk - Bk.conj().T) / 2j]:
                    a_entry = max(a_entry, np.linalg.norm(Hm, 2))
    a_entry *= 1.5
    N = k * d + extra
    Z = []
    for s in range(2):
        Jk = r.normal(size=(extra, extra)) + 1j * r.normal(size=(extra, extra))
        Jk = (Jk + Jk.conj().T) * 2
        C = np.zeros((N, N), complex)
        C[:k * d, :k * d] = Z0[s]
        C[k * d:, k * d:] = Jk
        F = r.normal(size=(N, junk_rank)) + 1j * r.normal(size=(N, junk_rank))
        F, _ = np.linalg.qr(F)
        C = C + F @ np.diag(r.uniform(-3, 3, junk_rank)) @ F.conj().T
        Z.append(C)
    G = r.normal(size=(N, N)) + 1j * r.normal(size=(N, N))
    Uh = polar_u(G)
    Z = [Uh @ z @ Uh.conj().T for z in Z]
    Z = [(z + z.conj().T) / 2 for z in Z]
    # 1. band projections of Z1
    w, Ev = np.linalg.eigh(Z[0])
    band = []
    for i in range(k):
        idx = np.where(np.abs(w - (i + 1)) < 0.5)[0]
        band.append(Ev[:, idx])
    # 2. truncated polar maps along the (path) tree from root band 0
    root = band[0]                       # N x dR orthonormal columns
    iota = {0: root}
    for (p, c) in edges:                 # path edges in BFS order
        Bm = band[c].conj().T @ Z[1] @ band[p]       # (dim c) x (dim p)
        u, s, vh = np.linalg.svd(Bm, full_matrices=False)
        good = (s >= 0.5) & (s <= 2.0)
        init = band[p] @ vh[good].conj().T           # N x g initial space
        fin = band[c] @ u[:, good]                   # N x g final space
        Pinit = init @ init.conj().T
        # restrict current root to vectors whose image under iota[p] lies in init
        coords = subspace_intersect(iota[p], Pinit)
        root = root @ coords
        for key in iota:
            iota[key] = iota[key] @ coords
        vmap = fin @ init.conj().T                   # partial isometry
        iota[c] = vmap @ iota[p]
    dR1 = root.shape[1]
    # 3. second truncation: Re/Im of entries minus D entries
    thresholds = []
    for _round in range(1):
        cur = np.eye(dR1, dtype=complex)
        for s in range(2):
            for i in range(k):
                for j in range(k):
                    Ent = iota[i].conj().T @ Z[s] @ iota[j] - Ds[s][i, j] * np.eye(dR1)
                    a = a_entry
                    for Hm in [(Ent + Ent.conj().T) / 2, (Ent - Ent.conj().T) / 2j]:
                        Hc = cur.conj().T @ Hm @ cur
                        ww, ee = np.linalg.eigh(Hc)
                        cur = cur @ ee[:, np.abs(ww) <= 2 * a]
        for key in iota:
            iota[key] = iota[key] @ cur
    dF = iota[0].shape[1]
    # 4. compressed pair in matrix units, distance to D
    Wp = [np.block([[iota[i].conj().T @ Z[s] @ iota[j] for j in range(k)] for i in range(k)]) for s in range(2)]
    dist = max(np.linalg.norm(Wp[s] - np.kron(Ds[s], np.eye(dF)), 2) for s in range(2))
    iso_err = max(np.abs(iota[i].conj().T @ iota[j] - (i == j) * np.eye(dF)).max() for i in range(k) for j in range(k))
    Vc, res = solve_tube(Wp, k, dF, Ds, V, O, H, pb, L)
    xr = [v / eps for v in Vc]
    m2 = max(abs(tr(xr[a] @ xr[b]) - tr(x[a] @ x[b])) for a in range(n) for b in range(n))
    m3 = max(abs(tr(xr[a] @ xr[b] @ xr[c]) - tr(x[a] @ x[b] @ x[c])) for a in range(3) for b in range(3) for c in range(3))
    m4 = max(abs(tr(xr[a] @ xr[a] @ xr[b] @ xr[b]) - tr(x[a] @ x[a] @ x[b] @ x[b])) for a in range(4) for b in range(4))
    return dict(k=k, N=N, N_mod_k=N % k, source_d=d, band_ranks=[b.shape[1] for b in band],
                root_after_polar=dR1, root_final=dF, rank_loss=N - k * dF,
                bad_dims_inserted=extra + junk_rank, op_dist_to_D=float(dist), eps=eps,
                entry_threshold_2a=float(2 * a_entry), bound_4k2a=float(4 * k * k * a_entry),
                isometry_err=float(iso_err), solver_residual=res,
                moment2_err=float(m2), moment3_err=float(m3), moment4_err=float(m4))


# ---------------- 5. unitary volumes ----------------
def logvolU(l):
    return l * (l + 1) / 2 * math.log(2 * math.pi) - sum(math.lgamma(j + 1) for j in range(1, l))


def volumes():
    c = 0.75 + 0.5 * math.log(2 * math.pi)
    out = []
    for l in [50, 200, 800, 3200]:
        out.append(dict(l=l, normalized_residual=(logvolU(l) - (-(l * l / 2) * math.log(l) + c * l * l)) / l**2))
    k = 3
    res = []
    for d in [100, 400, 1600]:
        lhs = (logvolU(k * d) - logvolU(d) - d * d / 2 * math.log(k)) / d**2
        rhs = -(k * k - 1) / 2 * math.log(d) - (k * k + 1) / 2 * math.log(k) + (k * k - 1) * c
        res.append(dict(d=d, A_d_residual_without_cD=lhs - rhs))
    return dict(unitary=out, quotient=res)


if __name__ == '__main__':
    out = dict(coarse=[coarse(k) for k in [2, 3]], noise=[noise(k) for k in [2, 3, 4]],
               almost_commute=[almost_commute(k) for k in [2, 3, 4]],
               recovery=[recovery(2, 60, 0, 0, 0.02, 1), recovery(2, 160, 3, 2, 0.02, 2),
                         recovery(3, 100, 4, 2, 0.02, 3), recovery(3, 100, 2, 1, 0.01, 4)],
               volumes=volumes(),
               scope="finite floating diagnostics only; no entropy limit, conjugate-variable existence or primary theorem is tested")
    print(json.dumps(out, indent=1, default=float))

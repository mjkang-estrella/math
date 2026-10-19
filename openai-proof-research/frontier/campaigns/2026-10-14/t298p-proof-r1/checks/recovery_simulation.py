"""Simulation of the arbitrary-size common-root recovery (matched-volume C, G).

A finite source tuple x (n=k^2+1 correlated Hermitian d0 x d0 matrices) is
encoded as Z = D(x)I + eps sum_a V_a (x) x_a, conjugated by a Haar unitary
(hiding all matrix units), corrupted by low-rank large outliers, and embedded in
size N = k d0 + extra (N not a multiple of k). The reviewer's implementation of
the candidate recovery is then run: spectral bands of Z_1, truncated tree-edge
polar maps, pulled-back common root, second common-root truncation of all
entry deviations, local normal-tube inverse. Reported: rank loss N - k d',
operator distance of the compressed pair to D(x)I, and the largest error in
normalized trace moments (words of length <= 3) between recovered and source
tuples. This is a finite diagnostic of the construction, not a proof.
"""
import json, sys, os, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import slice_bases

rng = np.random.default_rng(1104)

def expi(K):
    w, Q = np.linalg.eigh(K)
    return (Q * np.exp(1j * w)) @ Q.conj().T

def opn(x):
    return np.linalg.norm(x, 2) if x.size else 0.0

def herm(m):
    g = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
    return (g + g.conj().T) / (2 * math.sqrt(2 * m))  # approx standard GUE (norm ~2)

def null_intersection(bases):
    """Orthonormal basis of the intersection of column spans (all in same ambient)."""
    cur = bases[0]
    for b in bases[1:]:
        # vectors v = cur c with (I - b b*) cur c = 0
        M = cur - b @ (b.conj().T @ cur)
        u, s, vh = np.linalg.svd(M)
        null = vh[np.sum(s > 1e-8):].conj().T
        cur = cur @ null
        cur, _ = np.linalg.qr(cur) if cur.shape[1] else (cur, None)
    return cur

def run(k, d0, eps, n_out, extra):
    (D1, B), V, O, L, s, traceless, pair_basis = slice_bases(k, "path")
    edges = [(i, i + 1) for i in range(k - 1)]  # path tree rooted at band 0
    n = len(V)
    # correlated, non-free source tuple
    g = [herm(d0) for _ in range(n)]
    x = [g[a] + (0.3 * (g[0] @ g[0] - np.eye(d0)) if a % 3 == 1 else 0) for a in range(n)]
    x = [(xa + xa.conj().T) / 2 for xa in x]
    N0 = k * d0
    Z = [np.kron(Dt, np.eye(d0)) + eps * sum(np.kron(V[a][t], x[a]) for a in range(n)) for t, Dt in enumerate([D1, B])]
    Hq, _ = np.linalg.qr(rng.normal(size=(N0, N0)) + 1j * rng.normal(size=(N0, N0)))
    Z = [Hq @ z @ Hq.conj().T for z in Z]
    N = N0 + extra
    Zb = []
    for z in Z:
        big = np.zeros((N, N), dtype=complex)
        big[:N0, :N0] = z
        if extra:
            c = rng.normal(size=(N, extra)) + 1j * rng.normal(size=(N, extra))
            big[:, N0:] += 0.5 * c / math.sqrt(N)
            big[N0:, :] += 0.5 * c.conj().T / math.sqrt(N)
            big[N0:, N0:] += np.diag(rng.uniform(0.5, k + 0.5, size=extra))
        for _ in range(n_out):
            v = rng.normal(size=N) + 1j * rng.normal(size=N)
            v /= np.linalg.norm(v)
            big += rng.uniform(-3, 3) * np.outer(v, v.conj())
        Zb.append((big + big.conj().T) / 2)
    def recover(Zb, a_thr):
        Z1, Z2 = Zb
        N = Z1.shape[0]
        # 1. bands
        w, Q = np.linalg.eigh(Z1)
        bands = [Q[:, (w >= i + 0.5) & (w < i + 1.5)] for i in range(k)]
        # 2. truncated polar maps on tree edges (parent p -> child c)
        def tpolar(c, p):
            blk = bands[c].conj().T @ Z2 @ bands[p]
            u, sv, vh = np.linalg.svd(blk, full_matrices=False)
            good = (sv >= 0.5) & (sv <= 2.0)
            init = bands[p] @ vh[good].conj().T          # good initial subspace in band p (ambient coords)
            final = bands[c] @ u[:, good]
            return init, final  # partial isometry maps init[:,i] -> final[:,i]
        maps = {e: tpolar(e[1], e[0]) for e in edges}
        # 3. root space: pull back along path 0->1->...->k-1
        R = bands[0]
        def apply_path(Rb, j):
            cur = Rb
            for e in edges[:j]:
                init, final = maps[e]
                cur = final @ (init.conj().T @ cur)
            return cur
        for j in range(1, k):
            # vectors in R whose image after j-1 steps lies in init of edge j-1
            init, _ = maps[edges[j - 1]]
            img = apply_path(R, j - 1)
            M = img - init @ (init.conj().T @ img)
            u_, s_, vh_ = np.linalg.svd(M, full_matrices=True)
            null = vh_[np.sum(s_ > 1e-8):].conj().T
            R = R @ null
            R, _ = np.linalg.qr(R)
        phis = [apply_path(R, j) for j in range(k)]
        iso_err = max(np.abs(p.conj().T @ p - np.eye(R.shape[1])).max() for p in phis)
        # 4. entries and second truncation
        Dpair = [D1, B]
        def entries(phis_):
            return [[[p_i.conj().T @ Zb[t] @ p_j for p_j in phis_] for p_i in phis_] for t in range(2)]
        ent = entries(phis)
        devmax = 0.0
        goods = []
        dprime0 = R.shape[1]
        for t in range(2):
            for i in range(k):
                for j in range(k):
                    dev = ent[t][i][j] - Dpair[t][i, j] * np.eye(dprime0)
                    for H in [(dev + dev.conj().T) / 2, (dev - dev.conj().T) / 2j]:
                        lam, ev = np.linalg.eigh(H)
                        devmax = max(devmax, float(np.abs(lam).max()) if lam.size else 0.0)
                        goods.append(ev[:, np.abs(lam) <= a_thr])
        Rp = null_intersection(goods)
        phis2 = [p @ Rp for p in phis]
        dprime = Rp.shape[1]
        ent2 = entries(phis2)
        # compressed pair in C^k (x) R'
        Pz = [np.block([[ent2[t][i][j] for j in range(k)] for i in range(k)]) for t in range(2)]
        dist_D = max(opn(Pz[t] - np.kron(Dpair[t], np.eye(dprime))) for t in range(2))
        # 5. local normal-tube inverse (coefficientwise decomposition + fixed point)
        def pair_coords_scalar(p):
            return np.array([np.trace(pb[0] @ p[0] + pb[1] @ p[1]).real / k for pb in pair_basis])
        Mcols = [pair_coords_scalar((1j * (h @ D1 - D1 @ h), 1j * (h @ B - B @ h))) for h in traceless] + [pair_coords_scalar(v) for v in V]
        Minv = np.linalg.inv(np.column_stack(Mcols))
        def decompose(P, d):
            coeffs = []
            for pb in pair_basis:
                c = 0
                for t in range(2):
                    if np.abs(pb[t]).max() > 0:
                        X = np.kron(pb[t], np.eye(d)) @ P[t]
                        c = c + sum(X[i * d:(i + 1) * d, i * d:(i + 1) * d] for i in range(k)) / k
                coeffs.append(c)
            sol = np.einsum('ab,bij->aij', Minv, np.array(coeffs))
            nk = len(traceless)
            return sum(np.kron(traceless[b], sol[b]) for b in range(nk)), sol[nk:]
        Dk = [np.kron(D1, np.eye(dprime)), np.kron(B, np.eye(dprime))]
        W = [Pz[t] - Dk[t] for t in range(2)]
        K = np.zeros_like(Dk[0])
        for it in range(200):
            U = expi(K)
            C = [U.conj().T @ (Dk[t] + W[t]) @ U - Dk[t] for t in range(2)]
            dK, ycoef = decompose(C, dprime)
            K = K + dK
            if opn(dK) < 1e-12:
                break
        xr = [ycoef[a] / eps for a in range(n)]
        xr = [(y + y.conj().T) / 2 for y in xr]
        return dict(dprime0=dprime0, dprime=dprime, iso_err=iso_err, dist_D=dist_D, it=it, xr=xr, devmax=devmax, N=N)
    clean = recover([z.copy() for z in Z], 1e9)
    a_thr = 2 * clean["devmax"] + 1e-3
    r = recover(Zb, a_thr)
    dprime0, dprime, iso_err, dist_D, it, xr = r["dprime0"], r["dprime"], r["iso_err"], r["dist_D"], r["it"], r["xr"]
    # 6. moments
    trn = lambda m: np.trace(m).real / m.shape[0]
    words = [w_ for L_ in [1, 2, 3] for w_ in itertools.product(range(n), repeat=L_)]
    sel = [words[i] for i in rng.choice(len(words), size=min(400, len(words)), replace=False)]
    def mom(t, wd):
        m = np.eye(t[0].shape[0], dtype=complex)
        for a in wd:
            m = m @ t[a]
        return np.trace(m) / m.shape[0]
    merr = max(abs(mom(xr, wd) - mom(x, wd)) for wd in sel) if dprime > 0 else float('nan')
    clean_err = max(abs(mom(clean['xr'], wd) - mom(x, wd)) for wd in sel)
    scale = max(abs(mom(x, wd)) for wd in sel)
    return dict(k=k, d0=d0, N=N, eps=eps, outliers=n_out, extra_dims=extra,
                root_dim_after_first=int(dprime0), root_dim_final=int(dprime), rank_loss=int(N - k * dprime),
                path_isometry_err=float(iso_err), compressed_dist_to_D=float(dist_D), threshold_a=float(a_thr),
                solver_iterations=it, clean_model_exact_recovery_err=float(clean_err), clean_rank_loss=int(k * d0 - k * clean['dprime']), max_moment_err=float(merr), moment_scale=float(scale))

out = []
configs = [(2, 100, 0.02, 3, 1), (2, 200, 0.02, 3, 1), (2, 400, 0.02, 3, 1),
           (3, 150, 0.01, 2, 1), (3, 300, 0.01, 2, 1)]
for (k, d0, eps, n_out, extra) in configs:
    r = run(k, d0, eps, n_out, extra)
    r['rank_loss_fraction'] = r['rank_loss'] / r['N']
    out.append(r)
    assert r['path_isometry_err'] < 1e-10
    assert r['clean_model_exact_recovery_err'] < 1e-8 and r['clean_rank_loss'] == 0
    assert r['root_dim_final'] > 0 and r['compressed_dist_to_D'] <= 4 * k * r['threshold_a']
    # loss is bounded by a constant (outliers+extra) x (number of entry Hermitian parts), independent of N
    assert r['rank_loss'] <= k * (2 * (n_out + extra) * 4 * k * k + 2 * k)
for k in (2, 3):
    rs = [r for r in out if r['k'] == k]
    fr = [r['rank_loss_fraction'] for r in rs]
    me = [r['max_moment_err'] for r in rs]
    assert fr[-1] < fr[0] and me[-1] < me[0]
print(json.dumps(out, indent=1))

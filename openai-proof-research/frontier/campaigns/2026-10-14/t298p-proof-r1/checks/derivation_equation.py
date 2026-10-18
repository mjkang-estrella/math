"""Finite-algebra test of the derivation equation behind candidate inequality (3).

Coefficient algebra A = M_m (a genuine finite algebra, not a free-probability
model). N = M_k (x) A. Unknowns: inner-leg coefficients theta'_{a,bc} in A (x) A
for the normal derivations (theta' = eps*theta), and eta in N (x) N with matrix
part in ker(J)^perp. Equation, for each target j:
   sum_a (V_as (x) 1) . [sum_bc w_bc theta'_{a,bc}] + [Z_s, eta] = delta_js 1 (x) 1,
with Z_s = D_s + eps*(sum_a V_as (x) U_a + sum_b O_bs (x) T_b).
Checks: exact solvability, deviation of theta' and eta from their eps=0
values scales linearly in eps, and the solved derivation reproduces the target.
"""
import json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import E, slice_bases

def run(k, m, seed):
    rng = np.random.default_rng(seed)
    (D1, B), V, O, L, s, _, _ = slice_bases(k, "path")
    n = len(V)
    Ds = [D1, B]
    K = k * m
    def herm(scale=1.0):
        x = rng.normal(size=(m, m)) + 1j * rng.normal(size=(m, m))
        x = (x + x.conj().T) / 2
        return scale * x / np.linalg.norm(x, 2)
    U = [herm() for _ in range(n)]
    T = [herm() for _ in range(len(O))]
    Em = lambda u, v: E(m, u, v)
    # kernel of J (span w_bc) in M_k (x) M_k and an orthonormal complement
    wvecs = []
    for b in range(k):
        for c in range(k):
            t = np.zeros((k, k, k, k), dtype=complex)
            for i in range(k):
                t[i, b, c, i] = 1
            wvecs.append(t.reshape(-1))
    wvecs = np.array(wvecs).T
    qk, _ = np.linalg.qr(wvecs)
    P = np.eye(k**4) - qk @ qk.conj().T
    uu, _, _ = np.linalg.svd(P)
    comp = uu[:, :k**4 - k * k]
    def left(y, X):
        return np.einsum('pt,tqrs->pqrs', y, X)
    def right(X, y):
        return np.einsum('pqrt,ts->pqrs', X, y)
    # build columns
    def columns(eps):
        Zs = [np.kron(Ds[t], np.eye(m)) + eps * (sum(np.kron(V[a][t], U[a]) for a in range(n)) + sum(np.kron(O[b][t], T[b]) for b in range(len(O)))) for t in range(2)]
        cols = []
        labels = []
        for a in range(n):
            for b in range(k):
                for c in range(k):
                    for u in range(m):
                        for v in range(m):
                            for w_ in range(m):
                                for x in range(m):
                                    val = np.zeros((K, K, K, K), dtype=complex)
                                    for i in range(k):
                                        val += np.einsum('pq,rs->pqrs', np.kron(E(k, i, b), Em(u, v)), np.kron(E(k, c, i), Em(w_, x)))
                                    cols.append(np.concatenate([left(np.kron(V[a][t], np.eye(m)), val).reshape(-1) for t in range(2)]))
                                    labels.append(('n', a, b, c, u, v, w_, x))
        for q in range(comp.shape[1]):
            cm = comp[:, q].reshape(k, k, k, k)
            for u in range(m):
                for v in range(m):
                    for w_ in range(m):
                        for x in range(m):
                            eta = np.zeros((K, K, K, K), dtype=complex)
                            for i1 in range(k):
                                for j1 in range(k):
                                    for i2 in range(k):
                                        for j2 in range(k):
                                            cc = cm[i1, j1, i2, j2]
                                            if abs(cc) > 1e-15:
                                                eta += cc * np.einsum('pq,rs->pqrs', np.kron(E(k, i1, j1), Em(u, v)), np.kron(E(k, i2, j2), Em(w_, x)))
                            cols.append(np.concatenate([(left(Zs[t], eta) - right(eta, Zs[t])).reshape(-1) for t in range(2)]))
                            labels.append(('i', q, u, v, w_, x))
        return np.array(cols).T, labels
    one = np.einsum('pq,rs->pqrs', np.eye(K), np.eye(K))
    res = {}
    sols = {}
    for eps in [0.0, 0.01, 0.02, 0.04]:
        F, labels = columns(eps)
        assert F.shape[0] == F.shape[1]
        svals = np.linalg.svd(F, compute_uv=False)
        sj = []
        for j in range(2):
            target = np.concatenate([(one if t == j else 0 * one).reshape(-1) for t in range(2)])
            x = np.linalg.solve(F, target)
            assert np.abs(F @ x - target).max() < 1e-9
            sj.append(x)
        sols[eps] = (np.array(sj), labels, float(svals.min()))
    base = sols[0.0][0]
    labels = sols[0.0][1]
    nn = sum(1 for l in labels if l[0] == 'n')
    # eps=0 normal coefficient: (1/k)(V_aj)_{cb} * (1 (x) 1) in A (x) A
    lead_err = 0.0
    for j in range(2):
        for idx, l in enumerate(labels[:nn]):
            _, a, b, c, u, v, w_, x = l
            pred = V[a][j][c, b] / k if (u == v and w_ == x) else 0.0
            lead_err = max(lead_err, abs(base[j, idx] - pred))
    dev = {}
    for eps in [0.01, 0.02, 0.04]:
        d = sols[eps][0] - base
        dev[eps] = (float(np.abs(d[:, :nn]).max()), float(np.abs(d[:, nn:]).max()))
    ratio_n = dev[0.04][0] / dev[0.02][0]
    ratio_n2 = dev[0.02][0] / dev[0.01][0]
    return dict(k=k, m=m, unknowns=int(base.shape[1]), F_min_sv={str(e): sols[e][2] for e in sols},
                eps0_normal_coeff_err=float(lead_err),
                normal_dev={str(e): dev[e][0] for e in dev}, inner_dev={str(e): dev[e][1] for e in dev},
                normal_dev_doubling_ratios=[ratio_n2, ratio_n])

out = [run(2, 2, 11), run(2, 3, 12)]
for r in out:
    assert r['eps0_normal_coeff_err'] < 1e-10
    assert all(1.7 < q < 2.3 for q in r['normal_dev_doubling_ratios'])
print(json.dumps(out, indent=1))

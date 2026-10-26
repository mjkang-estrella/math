"""Explore actual source four-projection data through contractive cross-Gram matrices.

Numerical evidence only; no source conjecture or discovery is certified here.
For a+b=r, X=U*V is any r by r contraction. U and V are orthonormal
r-frames in C^(2r). Split U into ranks a,b and V into ranks b,a.
"""
from pathlib import Path
import json
import numpy as np

rng = np.random.default_rng(20261026)


def inverse_sqrt(g):
    values, vectors = np.linalg.eigh(g)
    if values[0] < 1e-8:
        raise ValueError("near a forbidden subspace intersection")
    return (vectors / np.sqrt(values)) @ vectors.conj().T


def score(x, a):
    r = len(x)
    b = r-a
    aa, bb = x[:a, :b], x[:a, b:]
    cc, dd = x[a:, :b], x[a:, b:]
    g1 = np.block([[np.eye(a), aa], [aa.conj().T, np.eye(b)]])
    g2 = np.block([[np.eye(b), dd], [dd.conj().T, np.eye(a)]])
    h = np.block([[np.zeros((a, b)), bb],
                  [cc.conj().T, np.zeros((b, a))]])
    hp = inverse_sqrt(g1) @ h @ inverse_sqrt(g2)
    lhs = float(np.sum(abs(aa)**2) + np.sum(abs(dd)**2))
    rhs = float(np.sum(abs(hp[:a, :b])**2) + np.sum(abs(hp[a:, b:])**2))
    return lhs, rhs


def project(x):
    # SVD is used only to obtain feasible contractions, not to assert a theorem.
    u, s, v = np.linalg.svd(x, full_matrices=False)
    return (u*np.minimum(s, 1-1e-9)) @ v


def rank_one_check(x):
    a, b, c, d = x[0,0], x[0,1], x[1,0], x[1,1]
    xx, yy = np.sqrt(1-abs(a)**2), np.sqrt(1-abs(d)**2)
    rhs = ((1-xx*yy)*(abs(b)**2+abs(c)**2)/2 +
           np.real(np.conj(a*d)*b*c))/(xx*xx*yy*yy)
    return float(rhs)


records = []
best = None
for r in range(2, 11):
    for a in sorted({1, r//2, r-1}):
        max_gap = -float("inf")
        max_ratio = 0.
        best_local = None
        for restart in range(8):
            z = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))
            x = project(z / np.linalg.norm(z, 2))
            left, right = score(x, a)
            objective = right-left
            for iteration in range(150):
                sigma = [0.15, 0.05, 0.01][min(iteration//50,2)]
                z = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))
                y = project(x + sigma*z/np.sqrt(r))
                try:
                    ll, rr = score(y,a)
                except ValueError:
                    continue
                # Keep a substantial overlap to avoid optimizing toward a zero-data limit.
                trial = rr-ll-0.2*max(0.,0.1-ll)**2
                current = objective-0.2*max(0.,0.1-left)**2
                if trial > current or rng.random() < 0.002:
                    x, left, right, objective = y, ll, rr, rr-ll
                if right-left > max_gap:
                    max_gap = right-left
                    best_local = x.copy()
                if left > 1e-8:
                    max_ratio = max(max_ratio,right/left)
                if r==2:
                    assert abs(rank_one_check(x)-right) < 1e-7
        left,right=score(best_local,a)
        item={"dimension":r,"rank_P":a,"rank_Q":r-a,
              "best_rhs_minus_lhs":max_gap,"lhs":left,"rhs":right,
              "largest_observed_ratio":max_ratio}
        records.append(item)
        print(json.dumps(item),flush=True)
        if best is None or max_gap > best[0]:
            best=(max_gap,best_local.copy(),a)

out={"status":"exploration only, not a proof","seed":20261026,
     "source":"Banica–Nechita arXiv1602.04456v3 Conjecture6.6",
     "records":records,"counterexample_detected":any(z["best_rhs_minus_lhs"]>1e-7 for z in records)}
folder=Path(__file__).resolve().parent
(folder/'screen.json').write_text(json.dumps(out,indent=2)+'\n')
np.savez(folder/'best-data.npz',cross_gram=best[1],rank_P=best[2])

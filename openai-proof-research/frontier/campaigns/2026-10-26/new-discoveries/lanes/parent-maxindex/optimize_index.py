#!/usr/bin/env python3
"""Exploratory alternating spectral maximization for source Conjecture4.19.

For x=sqrt(p), each fixed pair of top-k entry masks gives a quadratic
form in x. Replacing x by its leading eigenvector cannot decrease the
piecewise quadratic objective. This finds local optima only, not bounds.
"""
import json
import numpy as np


def select(x, k):
    p = x*x
    aa = (p[:, None] + p[None, :])/2
    gg = x[:, None]*x[None, :]
    ma, mg = np.zeros_like(aa), np.zeros_like(gg)
    ma.flat[np.argsort(aa, axis=None, kind="stable")[-k:]] = 1
    mg.flat[np.argsort(gg, axis=None, kind="stable")[-k:]] = 1
    c = (ma.sum(axis=0) + ma.sum(axis=1))/2
    return float((aa*ma).sum()+(gg*mg).sum()), np.diag(c)+(mg+mg.T)/2


def main():
    rng = np.random.default_rng(347947)
    results = []
    for d in [7, 8, 10, 15, 20, 30, 50, 100]:
        for offset in [-5, -4]:
            k, best = 2*d+offset, (-1., None)
            starts = [np.ones(d), np.r_[np.sqrt(d), np.ones(d-3), 0., 0.]]
            for _ in range(40):
                starts.append(np.exp(rng.normal(size=d)*rng.choice([.2, 1., 3.])))
            for x in starts:
                x = x/np.linalg.norm(x)
                for _ in range(80):
                    val, m = select(x, k)
                    if val > best[0]:
                        best = val, x.copy()
                    _, vec = np.linalg.eigh(m)
                    y = np.abs(vec[:, -1])
                    newval, _ = select(y, k)
                    assert newval >= val-1e-8
                    if np.linalg.norm(y-x) < 1e-12:
                        break
                    x = y
            row = {"dimension": d, "k": k, "max_found": best[0],
                   "gap_to_d": best[0]-d,
                   "p": sorted((best[1]**2).tolist(), reverse=True),
                   "qualification": "local numerical search only; no universal bound or exact counterexample"}
            results.append(row)
            print(f"d{d}, k{k}: max_found{best[0]:.15g}, gap{best[0]-d:.8g}", flush=True)
    print(json.dumps({"status": "exploratory only", "seed": 347947,
                      "starts_per_case": 42, "results": results,
                      "discovery_count_credit": 0}, indent=2))


if __name__ == "__main__":
    main()

"""Shapiro matrix exploration: F_p = Tr(sum A_i (A_{i+1}+A_{i+2})^{-1}).

Parametrization: 2x2 PD as A = L L^T, L = [[exp(x),0],[y,exp(z)]]  (3 params per matrix).
"""
import numpy as np
from scipy.optimize import minimize

def unpack(v, p):
    # 3 params per matrix: x (log diag), y (offdiag), z (log diag)
    Ls = []
    for i in range(p):
        x, y, z = v[3*i:3*i+3]
        L = np.array([[np.exp(x), 0.0], [y, np.exp(z)]])
        Ls.append(L)
    return Ls

def F_of_v(v, p, n_check=True):
    Ls = unpack(v, p)
    As = [L @ L.T for L in Ls]
    return F(As)

def F(As):
    p = len(As)
    n = As[0].shape[0]
    total = 0.0
    for i in range(p):
        S = As[(i+1) % p] + As[(i+2) % p]
        total += np.trace(As[i] @ np.linalg.inv(S))
    return total.real

def F_exact(As):
    """Use exact 2x2 inverse formula for stability."""
    p = len(As)
    total = 0.0
    for i in range(p):
        S = As[(i+1) % p] + As[(i+2) % p]
        a, b, c, d = S[0,0], S[0,1], S[1,0], S[1,1]
        det = a*d - b*c
        Sinv = np.array([[d, -b], [-c, a]]) / det
        total += np.trace(As[i] @ Sinv)
    return total.real

def rand_start(p, rng, scale=1.0):
    return rng.normal(0, scale, 3*p)

def search(p, n_trials=200, seed=0, pn2=None):
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    for t in range(n_trials):
        v0 = rand_start(p, rng)
        res = minimize(F_of_v, v0, args=(p,), method='L-BFGS-B',
                       options={'maxiter': 2000, 'ftol': 1e-15, 'gtol': 1e-12})
        val = F_of_v(res.x, p)
        if val < best[0]:
            best = (val, res.x.copy())
    return best

if __name__ == '__main__':
    import sys
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    n_trials = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    val, v = search(p, n_trials, seed)
    print(f"p={p} best F={val!r} target pn/2={p} (n=2) ratio={val/p!r}")
    np.save(f'best_p{p}_s{seed}.npy', v)

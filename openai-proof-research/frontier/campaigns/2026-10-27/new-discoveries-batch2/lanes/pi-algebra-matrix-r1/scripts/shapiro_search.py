"""Serious multistart search: inf Tr F_p over PD matrices (Cholesky params), p=5..7, n=2,3."""
import numpy as np
from scipy.optimize import minimize

def unpack(v, p, n):
    Ls = []
    k = 0
    for i in range(p):
        L = np.zeros((n, n))
        for c in range(n):
            L[c, c] = np.exp(np.clip(v[k], -30, 30)); k += 1
            for r in range(c+1, n):
                L[r, c] = np.clip(v[k], -30, 30); k += 1
        Ls.append(L)
    return Ls

def F_of_v(v, p, n):
    try:
        As = [L @ L.conj().T for L in unpack(v, p, n)]
        total = 0.0
        for i in range(p):
            S = As[(i+1) % p] + As[(i+2) % p]
            total += np.trace(As[i] @ np.linalg.inv(S)).real
        return total
    except np.linalg.LinAlgError:
        return 1e18

def search(p, n, trials, seed):
    rng = np.random.default_rng(seed)
    dim = p * (n*(n+1)//2)
    best = (np.inf, None)
    for t in range(trials):
        v0 = rng.normal(0, 1.0, dim)
        res = minimize(F_of_v, v0, args=(p, n), method='L-BFGS-B',
                       options={'maxiter': 3000, 'ftol': 1e-16, 'gtol': 1e-12})
        val = F_of_v(res.x, p, n)
        if val < best[0]:
            best = (val, res.x.copy())
    return best

if __name__ == '__main__':
    import sys
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    for p, n in [(5,2),(6,2),(5,3),(7,2)]:
        val, v = search(p, n, trials, seed)
        print(f"p={p} n={n}: best F={val:.9f}  pn/2={p*n/2:.1f}  gap={val - p*n/2:.3e}")
        if val < p*n/2:
            np.save(f'VIOLATION_p{p}_n{n}_s{seed}.npy', v)
            print("  *** SAVED VIOLATION ***")

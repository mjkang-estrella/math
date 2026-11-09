"""Diagonal subfamily: F = sum of two independent scalar Shapiro sums (n=2 diagonal)."""
import numpy as np
from scipy.optimize import minimize

def scalar_f(b, p):
    # b > 0 log-params; returns sum b_i/(b_{i+1}+b_{i+2}) via exp
    a = np.exp(b)
    s = 0.0
    for i in range(p):
        s += a[i]/(a[(i+1)%p] + a[(i+2)%p])
    return s

def search_scalar(p, trials=200, seed=0):
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    for t in range(trials):
        b0 = rng.normal(0, 1.5, p)
        res = minimize(scalar_f, b0, args=(p,), method='Nelder-Mead',
                       options={'maxiter': 20000, 'fatol': 1e-14, 'xatol': 1e-12})
        # polish with Powell
        res2 = minimize(scalar_f, res.x, args=(p,), method='Powell',
                        options={'maxiter': 20000, 'ftol': 1e-14, 'xtol': 1e-12})
        val = min(scalar_f(res.x,p), scalar_f(res2.x,p))
        x = res.x if scalar_f(res.x,p) < scalar_f(res2.x,p) else res2.x
        if val < best[0]:
            best = (val, x)
    return best

if __name__ == '__main__':
    import sys
    for p in [12, 13, 14, 15, 23]:
        val, x = search_scalar(p, trials=int(sys.argv[1]) if len(sys.argv)>1 else 60, seed=p)
        print(f"p={p}: scalar inf found = {val:.6f}  (p/2 = {p/2})")

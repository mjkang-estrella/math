# Numerical test whether a subset E of Z_p supports a unimodular sequence with perfect autocorrelation
# (equivalently: E is extreme in the sense of Graham, arXiv:1910.00924, Thm 2.2).
import sys; sys.path.append("/home/mj-kang/.local/lib/python3.14/site-packages")
import numpy as np, sys, json
from scipy.optimize import minimize
def objective(theta, E, p):
    c = np.zeros(p, complex); c[E] = np.exp(1j*theta)
    F = np.fft.fft(c); P = np.abs(F)**2 - len(E)
    val = np.sum(P**2)/p
    # gradient: d/dtheta_k of sum_chi (|F|^2-N)^2 = sum_chi 2(|F|^2-N) * d|F|^2
    # |F(chi)|^2 = sum_{x,y} c_x conj(c_y) w^{chi(x-y)}; d/dtheta_k = 2 Re( i c_k conj(F(chi)) w^{chi k} ... )
    w = np.exp(-2j*np.pi*np.outer(np.arange(p), E)/p)  # p x N
    dF2 = 2*np.real(1j*np.exp(1j*theta)[None, :]*w*np.conj(F)[:, None])
    grad = (2*P[:, None]*dF2).sum(0)/p
    return val, grad
def best(E, p, restarts, rng):
    E = np.array(E); bestv = 1e9; bestt = None
    for r in range(restarts):
        t0 = rng.uniform(0, 2*np.pi, len(E))
        res = minimize(objective, t0, args=(E, p), jac=True, method='BFGS', options={'gtol': 1e-12, 'maxiter': 2000})
        if res.fun < bestv: bestv, bestt = res.fun, res.x
        if bestv < 1e-18: break
    return bestv, bestt
if __name__ == '__main__':
    p = int(sys.argv[1]); sets = json.loads(sys.argv[2]); rs = int(sys.argv[3])
    rng = np.random.default_rng(1)
    for E in sets:
        v, t = best(E, p, rs, rng)
        print(p, len(E), E, 'min objective %.3e' % v)

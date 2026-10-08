"""Numerical sanity checks for proposals/analysis_geometry.md (Theorem HS-E).

Domain: Omega = f(D), f(z) = z + a z^(k+1), univalent for |a| < 1/(k+1), with
k-fold rotational symmetry. By conformal invariance of the Dirichlet integral and
of the Neumann condition, the Neumann problem on Omega pulls back to
    -Delta v = mu |f'|^2 v  in D,   d_r v = 0 on |z| = 1.
Galerkin in the L^2(D)-orthonormal Neumann-Bessel basis of D.

Checks (numerical evidence only, not proof):
  1. mu_1(Omega) is double (Ashbaugh-Benguria, Lemma 4.1);
  2. the Jacobian det D(u1,u2) has a constant sign in the interior and tends to 0 at the boundary;
  3. Phi = (u1,u2) is injective on a fine grid;
  4. every u in V vanishes at the centre, and Phi(Omega) is star-shaped about 0.

Run: python -I experiments/analysis_geometry.py   (needs numpy, scipy)
"""
import sys
import numpy as np
from scipy.special import jv, jvp, jnp_zeros
from scipy.linalg import eigh
from scipy.spatial import cKDTree


def basis(N, K):
    out = []  # (n, j, kind)
    for n in range(0, N + 1):
        zs = jnp_zeros(n, K) if n > 0 else jnp_zeros(0, K)  # n=0: nonzero zeros of J0'
        for j in zs:
            if n == 0:
                out.append((0, j, 'c'))
            else:
                out.append((n, j, 'c'))
                out.append((n, j, 's'))
    return out


def norm2(n, j):
    # int_0^1 J_n(j r)^2 r dr with J_n'(j) = 0
    return 0.5 * (1 - n * n / j ** 2) * jv(n, j) ** 2


def evalb(b, r, t, deriv=False):
    n, j, kind = b
    ang = np.cos(n * t) if kind == 'c' else np.sin(n * t)
    dang = -n * np.sin(n * t) if kind == 'c' else n * np.cos(n * t)
    c = 1.0 / np.sqrt(norm2(n, j) * (2 * np.pi if n == 0 else np.pi))
    R = jv(n, j * r)
    if not deriv:
        return c * R * ang
    return c * j * jvp(n, j * r) * ang, c * R * dang  # d_r, d_theta


def run(k, a, N=3 * 6, K=12, nr=80, nt=None):
    nt = nt or 8 * (N + 2) * 4
    B = basis(N, K)
    lam = np.array([b[1] ** 2 for b in B])
    xg, wg = np.polynomial.legendre.leggauss(nr)
    r = 0.5 * (xg + 1); wr = 0.5 * wg * r
    t = np.arange(nt) * 2 * np.pi / nt; wt = 2 * np.pi / nt
    RR, TT = np.meshgrid(r, t, indexing='ij')
    Z = RR * np.exp(1j * TT)
    w = np.abs(1 + a * (k + 1) * Z ** k) ** 2
    W = (wr[:, None] * wt) * w
    Phi = np.array([evalb(b, RR, TT).ravel() for b in B])
    # constant mode (mu=0) included so that mean-zero is enforced automatically
    one = np.full(RR.size, 1 / np.sqrt(np.pi))
    Phi = np.vstack([one, Phi]); lam = np.concatenate([[0.0], lam])
    M = (Phi * W.ravel()) @ Phi.T
    vals, vecs = eigh(np.diag(lam), M)
    return B, vals, vecs


def check(k, a, **kw):
    B, vals, vecs = run(k, a, **kw)
    mu = vals[1:5]
    print(f"k={k} a={a}: mu_1..mu_4 = {np.round(mu, 6)}  (mu_0={vals[0]:.1e})")
    C = vecs[1:, 1:3]  # coefficients of u1,u2 on non-constant basis (constant coeff in row 0)
    c0 = vecs[0, 1:3]
    # fine polar grid in the disk coordinates (Jacobian sign is conformally invariant)
    r = np.linspace(1e-3, 1 - 1e-3, 300); t = np.linspace(0, 2 * np.pi, 721)[:-1]
    RR, TT = np.meshgrid(r, t, indexing='ij')
    U = np.zeros((2,) + RR.shape); Ur = np.zeros_like(U); Ut = np.zeros_like(U)
    for i, b in enumerate(B):
        v = evalb(b, RR, TT); dr, dt = evalb(b, RR, TT, deriv=True)
        for m in range(2):
            U[m] += C[i, m] * v; Ur[m] += C[i, m] * dr; Ut[m] += C[i, m] * dt
    for m in range(2):
        U[m] += c0[m] / np.sqrt(np.pi)
    J = (Ur[0] * Ut[1] - Ut[0] * Ur[1]) / RR
    print(f"  Jacobian: min={J.min():.3e} max={J.max():.3e}; sign constant: {J.min() * J.max() > 0}")
    print(f"  |J| on r=0.999 / max|J|: {np.abs(J[-1]).max() / np.abs(J).max():.3e}")
    print(f"  |u_i(0)| (r=1e-3 ring max): {np.abs(U[:, 0, :]).max():.2e}  vs max|u|={np.abs(U).max():.2e}")
    # injectivity: image points that are very close must come from close domain points
    P = np.stack([U[0].ravel(), U[1].ravel()], 1)
    X = np.stack([(RR * np.cos(TT)).ravel(), (RR * np.sin(TT)).ravel()], 1)
    scale = np.abs(P).max()
    pairs = cKDTree(P).query_pairs(1e-3 * scale, output_type='ndarray')
    far = np.linalg.norm(X[pairs[:, 0]] - X[pairs[:, 1]], axis=1).max() if len(pairs) else 0
    print(f"  injectivity: {len(pairs)} image pairs within 1e-3*scale; max domain separation {far:.3e}")
    # star-shapedness about 0: along each ray direction w, nodal arc of u_e maps into the line;
    # test that the radial function of the image boundary is single valued: angle of Phi on the
    # boundary circle is monotone (winding 1, no backtracking)
    ang = np.unwrap(np.arctan2(U[1, -1], U[0, -1]))
    d = np.diff(ang)
    print(f"  boundary winding = {(ang[-1] - ang[0] + d.mean()) / (2 * np.pi):.3f}; "
          f"angle monotone on boundary: {np.all(d > 0) or np.all(d < 0)}")
    return vals


if __name__ == '__main__':
    for (k, a) in [(3, 0.0), (3, 0.15), (3, 0.24), (4, 0.18), (5, 0.12)]:
        check(k, a)
    # convergence check
    print('convergence, k=3 a=0.24:')
    for N, K in [(12, 8), (18, 12), (24, 16)]:
        _, v, _ = run(3, 0.24, N=N, K=K)
        print(f"  N={N} K={K}: mu1,mu2,mu3 = {np.round(v[1:4], 7)}")
    sys.exit(0)

import itertools
import math
import sys

import numpy as np
from scipy.spatial import ConvexHull


def cn(n):
    return (n + 1) * n ** n / math.factorial(n)


def area_vectors(V):
    """Facet area vectors (outward) of conv(V), merged by facet hyperplane."""
    n = V.shape[1]
    V = V - V.mean(0)
    C = np.cov(V.T) + 1e-300 * np.eye(n)
    L = np.linalg.cholesky(np.linalg.inv(C))
    V = V @ L  # affine whitening; R is affine invariant
    hull = ConvexHull(V)
    groups = {}
    for simp, eq in zip(hull.simplices, hull.equations):
        P = V[simp]
        M = (P[1:] - P[0]).T  # n x (n-1)
        # generalized cross product: component k = (-1)^k det(M without row k)
        c = np.array([(-1) ** k * np.linalg.det(np.delete(M, k, axis=0)) for k in range(n)])
        c /= math.factorial(n - 1)
        if c @ eq[:n] < 0:
            c = -c
        key = tuple(np.round(eq[:n], 6))
        groups[key] = groups.get(key, 0) + c
    return np.array(list(groups.values())), hull.volume


def zono_vol(G):
    m, n = G.shape
    if m < n:
        return 0.0
    idx = np.array(list(itertools.combinations(range(m), n)))
    return np.abs(np.linalg.det(G[idx])).sum()


def R(V):
    G, vol = area_vectors(V)
    n = V.shape[1]
    if np.abs(G.sum(0)).max() > 1e-8 * np.abs(G).max():
        raise ValueError("area vectors do not close")
    return zono_vol(G) / vol ** (n - 1)


if __name__ == "__main__":
    for n in range(2, 7):
        S = np.vstack([np.zeros(n), np.eye(n)])
        print(n, R(S), cn(n))

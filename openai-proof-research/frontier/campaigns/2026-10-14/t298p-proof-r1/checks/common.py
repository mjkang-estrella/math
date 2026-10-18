"""Shared finite constructions for the T298P proof-review diagnostics.

Independent reviewer code (not derived from the author's diagnostics).
All inner products use normalized traces tr_k unless stated otherwise.
"""
import numpy as np


def E(k, i, j):
    m = np.zeros((k, k), dtype=complex)
    m[i, j] = 1.0
    return m


def tree_pair(k, tree="path"):
    D1 = np.diag(np.arange(1, k + 1)).astype(complex)
    B = np.zeros((k, k), dtype=complex)
    if tree == "path":
        edges = [(i, i + 1) for i in range(k - 1)]
    elif tree == "star":
        edges = [(0, i) for i in range(1, k)]
    else:
        raise ValueError(tree)
    for i, j in edges:
        B[i, j] = B[j, i] = 1.0
    return D1, B, edges


def herm_basis(k):
    """Real basis of Hermitian k x k matrices, orthonormal for tr_k(AB)."""
    out = []
    for i in range(k):
        out.append(np.sqrt(k) * E(k, i, i))
    for i in range(k):
        for j in range(i + 1, k):
            out.append(np.sqrt(k / 2) * (E(k, i, j) + E(k, j, i)))
            out.append(np.sqrt(k / 2) * 1j * (E(k, i, j) - E(k, j, i)))
    return out


def tr(a):
    return np.trace(a) / a.shape[0]


def slice_bases(k, tree="path"):
    """Orbit/normal decomposition of the pair space at D=(D1,B).

    Returns D-pair, list of orthonormal normal pairs V_a, list of orthonormal
    orbit pairs O_b, and the tangent map matrix L (pair coords x traceless coords).
    """
    D1, B, edges = tree_pair(k, tree)
    H = herm_basis(k)
    pair_basis = [(h, np.zeros_like(h)) for h in H] + [(np.zeros_like(h), h) for h in H]
    # traceless Hermitian basis: orthogonal complement of identity in H
    Hmat = np.array([h.reshape(-1) for h in H]).T  # columns
    ident = np.eye(k).reshape(-1)
    coeff_id = np.array([tr(h).real for h in H])  # tr_k(h * I)
    # orthonormal basis of complement of coeff_id in R^{k^2}
    q, _ = np.linalg.qr(np.column_stack([coeff_id / np.linalg.norm(coeff_id), np.eye(k * k)]))
    T0 = q[:, 1:k * k]
    traceless = [sum(T0[a, b] * H[a] for a in range(k * k)) for b in range(k * k - 1)]
    def pair_coords(p):
        return np.array([tr(pb[0].conj().T @ p[0] + pb[1].conj().T @ p[1]).real for pb in pair_basis])
    L = np.column_stack([pair_coords((1j * (h @ D1 - D1 @ h), 1j * (h @ B - B @ h))) for h in traceless])
    u, s, vt = np.linalg.svd(L, full_matrices=True)
    r = int(np.sum(s > 1e-10))
    orbit_coords = u[:, :r]
    normal_coords = u[:, r:]
    def to_pair(c):
        return (sum(c[i] * pair_basis[i][0] for i in range(2 * k * k)),
                sum(c[i] * pair_basis[i][1] for i in range(2 * k * k)))
    V = [to_pair(normal_coords[:, a]) for a in range(normal_coords.shape[1])]
    O = [to_pair(orbit_coords[:, b]) for b in range(orbit_coords.shape[1])]
    return (D1, B), V, O, L, s, traceless, pair_basis

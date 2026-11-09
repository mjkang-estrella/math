"""Shared routines for the four-projection conjecture (MathDB 332493 / arXiv:1602.04456v3 Conjecture 6.6).

Configurations are given by isometry frames:
  p: K x a  (frame of P),  q: K x b (frame of Q),
  r: K x b  (frame of R),  s: K x a (frame of S),
with p^*q = 0, r^*s = 0 (orthogonality hypotheses 1,2).

Canonical realization of an arbitrary contraction X = [[A,B],[F,D]]
(A: a x b, B: a x a, F: b x b, D: b x a), ||A||<1, ||D||<1:
  K = 2(a+b), U = [I_{a+b}; 0], V = [X; (I - X^*X)^{1/2}],
  p = U[:, :a], q = U[:, a:], r = V[:, :b], s = V[:, b:].
Then p^*q=0, r^*s=0 automatically (U, V isometries), and the four cross blocks are A,B,F,D.
"""
import numpy as np


def inverse_sqrt(g):
    """Inverse square root of Hermitian PSD matrix via eigendecomposition."""
    val, vec = np.linalg.eigh(g)
    val = np.maximum(val, 1e-300)
    return (vec / np.sqrt(val)) @ vec.conj().T


def sqrtm_psd(g):
    val, vec = np.linalg.eigh(g)
    val = np.maximum(val, 0.0)
    return (vec * np.sqrt(val)) @ vec.conj().T


def canonical_from_X(X):
    """Return p,q,r,s from contraction X. X must be (a+b)x(a+b) with block shapes
    [[a x b, a x a],[b x b, b x a]]."""
    n = X.shape[0]
    # n = a+b ; a = ? we read off from block shapes: A is X[:a, :b] -> a rows, b cols.
    # We need (a, b) passed or inferred; here we require caller passes (a, b).
    raise NotImplementedError


def canonical_from_X(X, a, b):
    n = a + b
    assert X.shape == (n, n)
    Xd = X.astype(complex)
    w, v = np.linalg.eigh(Xd.conj().T @ Xd)
    w = np.maximum(w, 0.0)
    # (I - X*X)^{1/2} on the complement; X*X has eigenvectors v, eigenvalues w
    # sqrt(I - X*X) = V diag(sqrt(1-w)) V^*  with eigenvalue 1 on ker(X*X)
    root = (v * np.sqrt(np.maximum(1.0 - w, 0.0))) @ v.conj().T
    V = np.vstack([Xd, root])          # 2n x n
    U = np.vstack([np.eye(n), np.zeros((n, n))])
    p = U[:, :a]
    q = U[:, a:]
    r = V[:, :b]
    s = V[:, b:]
    return p, q, r, s


def direct_traces(p, q, r, s):
    """Direct computation of Tr(P'Q') + Tr(R'S') and Tr(PR)+Tr(QS)
    from frames, using (P+R)^{-1/2} = [p r] G1^{-3/2} [p r]^* and
    P' = (P+R)^{-1/2} P (P+R)^{-1/2} = [p r] G1^{-1/2} E_p G1^{-1/2} [p r]^*."""
    P = p @ p.conj().T
    Q = q @ q.conj().T
    R = r @ r.conj().T
    S = s @ s.conj().T
    lhs = np.trace(P @ R).real + np.trace(Q @ S).real

    # P' = (P+R)^{-1/2} P (P+R)^{-1/2} directly via eigh of P+R (rank a+b)
    def whitened_traces(A_pos, Xa_frame, B_pos, Xb_frame):
        """Return Tr(X_a' X_b') where X_a' = (A_pos)^{-1/2} X_a (A_pos)^{-1/2}."""
        # A_pos = M M^* with M = [frame columns]; M^* M = G > 0 (no intersection)
        # Truncate eigenvalues below tolerance to zero (rank-deficient case).
        val, vec = np.linalg.eigh(A_pos)
        inv = np.where(val > 1e-10 * max(val.max(), 1.0), 1.0 / np.sqrt(np.maximum(val, 1e-300)), 0.0)
        Ah = (vec * inv) @ vec.conj().T  # A_pos^{-1/2} (Moore-Penrose)
        Xa = Ah @ Xa_frame @ Xa_frame.conj().T @ Ah
        Xb = Ah @ Xb_frame @ Xb_frame.conj().T @ Ah
        return np.trace(Xa @ Xb).real

    t1 = whitened_traces(P + R, P, Q + S, Q)
    t2 = whitened_traces(P + R, R, Q + S, S)
    return lhs, t1 + t2


def block_formula(X, a, b):
    """Reduced formula: LHS = ||A||_F^2 + ||D||_F^2,
    RHS = ||Z11||_F^2 + ||Z22||_F^2, Z = G1^{-1/2} M G2^{-1/2},
    G1 = [[I_a, A],[A^*, I_b]], G2 = [[I_b, D],[D^*, I_a]], M = [[0, B],[F^*, 0]]."""
    A = X[:a, :b]
    B = X[:a, b:]
    F = X[a:, :b]
    D = X[a:, b:]
    G1 = np.block([[np.eye(a), A], [A.conj().T, np.eye(b)]])
    G2 = np.block([[np.eye(b), D], [D.conj().T, np.eye(a)]])
    M = np.block([[np.zeros((a, b)), B], [F.conj().T, np.zeros((b, a))]])
    Z = inverse_sqrt(G1) @ M @ inverse_sqrt(G2)
    lhs = np.linalg.norm(A, 'fro') ** 2 + np.linalg.norm(D, 'fro') ** 2
    rhs = np.linalg.norm(Z[:a, :b], 'fro') ** 2 + np.linalg.norm(Z[a:, b:], 'fro') ** 2
    return lhs, rhs


def random_contraction(a, b, rng, margin=0.9):
    n = a + b
    # random complex matrix, compress to contraction with ||A||,||D|| < 1
    X = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / np.sqrt(2)
    X = project_contraction(X, margin)
    return X


def project_contraction(X, margin=0.9):
    """Project to contraction with spectral norm <= margin (keeps ||A||,||D||<1 strictly)."""
    u, sv, vh = np.linalg.svd(X)
    sv = np.minimum(sv, margin)
    return (u * sv) @ vh

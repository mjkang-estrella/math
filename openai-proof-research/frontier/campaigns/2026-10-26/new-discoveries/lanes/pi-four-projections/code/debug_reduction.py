"""Debug the reduction mismatch on near-singular configurations."""
import sys, numpy as np
sys.path.insert(0, 'code')
from common import inverse_sqrt, sqrtm_psd

rng = np.random.default_rng(7)

def random_frames(a, b, K, rng):
    n = a + b
    Q1, _ = np.linalg.qr(rng.standard_normal((K, K)) + 1j*rng.standard_normal((K, K)))
    U = Q1[:, :n]
    Q2, _ = np.linalg.qr(rng.standard_normal((K, K)) + 1j*rng.standard_normal((K, K)))
    r = Q2[:, :b]
    Pcomp = np.eye(K) - r @ r.conj().T
    Qc, _ = np.linalg.qr(Pcomp @ rng.standard_normal((K, K)) + 1j*Pcomp @ rng.standard_normal((K, K)))
    s = Qc[:, :a]
    p = U[:, :a]; q = U[:, a:]
    return p, q, r, s

def whitened_trace_direct(Ppos, Fa, Fb, tol_rel=1e-10):
    val, vec = np.linalg.eigh(Ppos)
    inv = np.where(val > tol_rel * max(val.max(), 1.0), 1.0/np.sqrt(np.maximum(val,1e-300)), 0.0)
    Ah = (vec * inv) @ vec.conj().T
    Xa = Ah @ Fa @ Fa.conj().T @ Ah
    Xb = Ah @ Fb @ Fb.conj().T @ Ah
    return np.trace(Xa @ Xb).real

def whitened_trace_frames(Mab, Ea, Gb, Eb):
    """Tr(P'Q') via frames: M = [fa, fb] (K x n), Gram Gab; same for other pair.
    P' = Mab Gab^{-1/2} Ea Gab^{-1/2} Mab^*; Tr = Tr(Gab^{-1/2} Ea Gab^{-1/2} Mab^* Mbb Gbb^{-1/2} Eb ...)"""
    raise NotImplementedError

for trial in range(60):
    a = int(rng.integers(1, 4)); b = int(rng.integers(1, 4))
    K = 2*(a+b)
    p, q, r, s = random_frames(a, b, K, rng)
    U = np.hstack([p, q]); V = np.hstack([r, s])
    X = U.conj().T @ V
    A = X[:a, :b]; B = X[:a, b:]; F = X[a:, :b]; D = X[a:, b:]
    G1 = np.block([[np.eye(a), A],[A.conj().T, np.eye(b)]])
    G2 = np.block([[np.eye(b), D],[D.conj().T, np.eye(a)]])
    ev1 = np.linalg.eigvalsh(G1); ev2 = np.linalg.eigvalsh(G2)
    if trial in (58, 59):
        print(f"trial {trial} a={a} b={b}")
        print("  G1 eigenvalues:", ev1)
        print("  G2 eigenvalues:", ev2)
        print("  |A| spectral:", np.linalg.svd(A, compute_uv=False))
        print("  |D| spectral:", np.linalg.svd(D, compute_uv=False))
        # direct
        P = p@p.conj().T; Q = q@q.conj().T; R = r@r.conj().T; S = s@s.conj().T
        t1 = whitened_trace_direct(P+R, P, Q+S)
        t2 = whitened_trace_direct(P+R, R, Q+S)
        lhs = np.trace(P@R).real + np.trace(Q@S).real
        M = np.block([[np.zeros((a,b)), B],[F.conj().T, np.zeros((b,a))]])
        Z = inverse_sqrt(G1) @ M @ inverse_sqrt(G2)
        rhs_b = np.linalg.norm(Z[:a,:b],'fro')**2 + np.linalg.norm(Z[a:,b:],'fro')**2
        print(f"  direct rhs={t1+t2:.8f}  block rhs={rhs_b:.8f}  lhs={lhs:.8f}")

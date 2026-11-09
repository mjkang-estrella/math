"""Replicate verify_reduction.py's exact rng stream, dump failing configs,
compare three computations of Tr(P'Q') + Tr(R'S'):
  (1) direct eigh of P+R, Q+S (truncated Moore-Penrose inverse sqrt)
  (2) block formula ||Z11||^2 + ||Z22||^2
  (3) explicit K x K matrices P', Q' via P' = W G1^{-1/2} E_p G1^{-1/2} W*
"""
import sys, numpy as np
sys.path.insert(0, 'code')
from common import canonical_from_X, random_contraction, inverse_sqrt

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

def mp_inv_sqrt(Apos, rel=1e-10):
    val, vec = np.linalg.eigh(Apos)
    inv = np.where(val > rel * max(val.max(), 1.0), 1.0/np.sqrt(np.maximum(val,1e-300)), 0.0)
    return (vec * inv) @ vec.conj().T

fails = []
# canonical section (same rng consumption as verify_reduction.py)
for trial in range(60):
    a = int(rng.integers(1, 4)); b = int(rng.integers(1, 4))
    X = random_contraction(a, b, rng, margin=rng.uniform(0.5, 0.99))
    p, q, r, s = canonical_from_X(X, a, b)
    P = p@p.conj().T; Q = q@q.conj().T; R = r@r.conj().T; S = s@s.conj().T
    Wp = mp_inv_sqrt(P+R); Wq = mp_inv_sqrt(Q+S)
    Pp = Wp@P@Wp; Qp = Wq@Q@Wq; Rp = Wp@R@Wp; Sp = Wq@S@Wq
    rhs_direct = np.trace(Pp@Qp).real + np.trace(Rp@Sp).real
    lhs = np.trace(P@R).real + np.trace(Q@S).real
    A = X[:a,:b]; B = X[:a,b:]; F = X[a:,:b]; D = X[a:,b:]
    G1 = np.block([[np.eye(a), A],[A.conj().T, np.eye(b)]])
    G2 = np.block([[np.eye(b), D],[D.conj().T, np.eye(a)]])
    M = np.block([[np.zeros((a,b)), B],[F.conj().T, np.zeros((b,a))]])
    Z = inverse_sqrt(G1) @ M @ inverse_sqrt(G2)
    rhs_block = np.linalg.norm(Z[:a,:b],'fro')**2 + np.linalg.norm(Z[a:,b:],'fro')**2
    lhs_block = np.linalg.norm(A,'fro')**2 + np.linalg.norm(D,'fro')**2
    e = max(abs(rhs_direct-rhs_block), abs(lhs-lhs_block))
    if e > 1e-9: fails.append(('canon', trial, a, b, e))
print("canonical fails:", fails)

# random frames section
fails2 = []
configs = []
for trial in range(60):
    a = int(rng.integers(1, 4)); b = int(rng.integers(1, 4))
    K = 2*(a+b)
    p, q, r, s = random_frames(a, b, K, rng)
    U = np.hstack([p, q]); V = np.hstack([r, s])
    X = U.conj().T @ V
    P = p@p.conj().T; Q = q@q.conj().T; R = r@r.conj().T; S = s@s.conj().T
    Wp = mp_inv_sqrt(P+R); Wq = mp_inv_sqrt(Q+S)
    Pp = Wp@P@Wp; Qp = Wq@Q@Wq; Rp = Wp@R@Wp; Sp = Wq@S@Wq
    rhs_direct = np.trace(Pp@Qp).real + np.trace(Rp@Sp).real
    lhs = np.trace(P@R).real + np.trace(Q@S).real
    A = X[:a,:b]; B = X[:a,b:]; F = X[a:,:b]; D = X[a:,b:]
    G1 = np.block([[np.eye(a), A],[A.conj().T, np.eye(b)]])
    G2 = np.block([[np.eye(b), D],[D.conj().T, np.eye(a)]])
    M = np.block([[np.zeros((a,b)), B],[F.conj().T, np.zeros((b,a))]])
    Z = inverse_sqrt(G1) @ M @ inverse_sqrt(G2)
    rhs_block = np.linalg.norm(Z[:a,:b],'fro')**2 + np.linalg.norm(Z[a:,b:],'fro')**2
    lhs_block = np.linalg.norm(A,'fro')**2 + np.linalg.norm(D,'fro')**2
    # method 3: explicit frame matrices
    W = np.hstack([p, r]); W2 = np.hstack([q, s])
    G1f = W.conj().T@W; G2f = W2.conj().T@W2
    Ep = np.zeros((a+b, a+b)); Ep[:a,:a] = np.eye(a)
    Eq = np.zeros((b+a, b+a)); Eq[:b,:b] = np.eye(b)
    Pp3 = W @ inverse_sqrt(G1f) @ Ep @ inverse_sqrt(G1f) @ W.conj().T
    Qp3 = W2 @ inverse_sqrt(G2f) @ Eq @ inverse_sqrt(G2f) @ W2.conj().T
    Er = np.zeros((a+b, a+b)); Er[a:,a:] = np.eye(b)
    Es = np.zeros((b+a, b+a)); Es[b:,b:] = np.eye(a)
    Rp3 = W @ inverse_sqrt(G1f) @ Er @ inverse_sqrt(G1f) @ W.conj().T
    Sp3 = W2 @ inverse_sqrt(G2f) @ Es @ inverse_sqrt(G2f) @ W2.conj().T
    rhs_frames = np.trace(Pp3@Qp3).real + np.trace(Rp3@Sp3).real
    e = max(abs(rhs_direct-rhs_block), abs(lhs-lhs_block), abs(rhs_direct-rhs_frames))
    if e > 1e-9:
        fails2.append((trial, a, b, e, rhs_direct, rhs_block, rhs_frames, lhs, lhs_block))
        configs.append((a,b,p,q,r,s))
for f in fails2:
    print("FAIL trial=%d a=%d b=%d err=%.3e\n  direct=%.8f block=%.8f frames=%.8f lhs=%.8f lhs_block=%.8f" % f)
if not fails2: print("all random-frame trials pass")

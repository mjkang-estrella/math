"""Verify the reduction: block formula vs direct projection computation.

For random canonical realizations of contractions X, check
  direct Tr(P'Q') + Tr(R'S')  ==  ||Z11||_F^2 + ||Z22||_F^2
  direct Tr(PR) + Tr(QS)      ==  ||A||_F^2 + ||D||_F^2.
"""
import sys, numpy as np
sys.path.insert(0, 'code')
from common import canonical_from_X, direct_traces, block_formula, random_contraction, inverse_sqrt

rng = np.random.default_rng(7)
worst = 0.0
for trial in range(60):
    a = int(rng.integers(1, 4)); b = int(rng.integers(1, 4))
    X = random_contraction(a, b, rng, margin=rng.uniform(0.5, 0.99))
    p, q, r, s = canonical_from_X(X, a, b)
    # hypotheses check
    assert np.abs(p.conj().T @ q).max() < 1e-10, "p perp q"
    assert np.abs(r.conj().T @ s).max() < 1e-10, "r perp s"
    lhs_d, rhs_d = direct_traces(p, q, r, s)
    lhs_b, rhs_b = block_formula(X, a, b)
    e1 = abs(lhs_d - lhs_b); e2 = abs(rhs_d - rhs_b)
    worst = max(worst, e1, e2)
    if e1 > 1e-9 or e2 > 1e-9:
        print(f"trial {trial}: a={a} b={b} lhs_d={lhs_d:.10f} lhs_b={lhs_b:.10f} rhs_d={rhs_d:.10f} rhs_b={rhs_b:.10f}")
print("worst abs error:", worst)

# Also verify with explicitly random (non-canonical) frames satisfying constraints.
print("--- random frames with constraints ---")
def random_frames(a, b, K, rng):
    # U isometry: first a+b columns of random unitary
    n = a + b
    assert K >= n
    Q1, _ = np.linalg.qr(rng.standard_normal((K, K)) + 1j*rng.standard_normal((K, K)))
    U = Q1[:, :n]
    # V: random isometry with column blocks orthogonal: take random unitary, but need r*s=0:
    # r (b cols) and s (a cols) with r^*s=0. Take V = Q2[:, :n] won't give it.
    # Instead: pick r any isometry K->C^b, then s isometry into range(r)^\perp.
    Q2, _ = np.linalg.qr(rng.standard_normal((K, K)) + 1j*rng.standard_normal((K, K)))
    r = Q2[:, :b]
    # complement basis to range(r)
    # orthonormal complement via QR of projection
    Pcomp = np.eye(K) - r @ r.conj().T
    Qc, _ = np.linalg.qr(Pcomp @ rng.standard_normal((K, K)) + 1j*Pcomp @ rng.standard_normal((K, K)))
    # columns of Qc spanning range(Pcomp) (first K-b or so); need a of them
    s = Qc[:, :a]
    # verify s isometry and r perp s
    assert np.abs(r.conj().T @ s).max() < 1e-10
    assert np.abs(s.conj().T @ s - np.eye(a)).max() < 1e-10
    p = U[:, :a]; q = U[:, a:]
    return p, q, r, s

worst2 = 0.0
for trial in range(60):
    a = int(rng.integers(1, 4)); b = int(rng.integers(1, 4))
    K = 2*(a+b)
    p, q, r, s = random_frames(a, b, K, rng)
    lhs_d, rhs_d = direct_traces(p, q, r, s)
    # block formula from X = U*V with U=[p q], V=[r s]
    U = np.hstack([p, q]); V = np.hstack([r, s])
    X = U.conj().T @ V
    lhs_b, rhs_b = block_formula(X, a, b)
    e1 = abs(lhs_d - lhs_b); e2 = abs(rhs_d - rhs_b)
    worst2 = max(worst2, e1, e2)
    if e1 > 1e-9 or e2 > 1e-9:
        print(f"trial {trial}: a={a} b={b} lhs_d={lhs_d:.10f} lhs_b={lhs_b:.10f} rhs_d={rhs_d:.10f} rhs_b={rhs_b:.10f}")
print("worst abs error (random frames):", worst2)

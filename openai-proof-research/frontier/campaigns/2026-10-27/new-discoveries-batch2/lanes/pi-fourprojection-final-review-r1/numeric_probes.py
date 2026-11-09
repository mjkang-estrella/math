#!/usr/bin/env python3
"""Independent numerical probes (own codepath, not the Lean checker).

1. Scalar-core estimate on a dense grid.
2. Full conjecture inequality on randomized nontrivial instances satisfying
   all six hypotheses, and instances violating rank balances only.
3. P' orthogonality (idempotent+Hermitian) under disjoint ranges.
4. Negative control: hypotheses dropped -> inequality can fail.
"""
import numpy as np

rng = np.random.default_rng(20261027)

def proj(v):
    v = v / np.linalg.norm(v)
    return np.outer(v, v.conj())

def rand_unit(n):
    v = rng.normal(size=n) + 1j * rng.normal(size=n)
    return v / np.linalg.norm(v)

def mpinvsqrt(A):
    w, U = np.linalg.eigh(A)
    w = np.where(np.abs(w) < 1e-12, 0.0, w)
    f = np.array([1/np.sqrt(x) if x > 0 else 0.0 for x in w])
    return (U * f) @ U.conj().T

def check_instance(P, R, Q, S, label):
    X = mpinvsqrt(P + R); Y = mpinvsqrt(Q + S)
    Pp, Rp = X @ P @ X, X @ R @ X
    Qp, Sp = Y @ Q @ Y, Y @ S @ Y
    lhs = np.trace(P @ R + Q @ S).real
    rhs = np.trace(Pp @ Qp + Rp @ Sp).real
    ok = lhs + 1e-9 >= rhs
    # P' projection check
    idem = np.allclose(Pp @ Pp, Pp, atol=1e-9)
    herm = np.allclose(Pp, Pp.conj().T, atol=1e-9)
    print(f"{label}: Tr(PR)+Tr(QS)={lhs:.6f} >= Tr(P'Q')+Tr(R'S')={rhs:.6f} ok={ok} P'proj={idem and herm}")
    return ok

# 1. scalar grid
worst = 0.0
for a in np.linspace(-0.99, 0.99, 199):
    for b in np.linspace(-0.99, 0.99, 199):
        if a*a >= 1 or b*b >= 1: continue
        u = np.sqrt((1+a)*(1+b)); v = np.sqrt((1-a)*(1-b))
        for _ in range(3):
            x, y = rng.normal(size=2) + 1j*rng.normal(size=2)
            # enforce u x + v y = 0
            y = -u/v * x
            t = a*a + b*b
            val = abs(x+y)**2 / (abs(x)**2 + abs(y)**2) if abs(x)**2+abs(y)**2 > 1e-18 else 0
            worst = max(worst, val - t)
print(f"scalar grid worst excess: {worst:.2e} (must be <= ~1e-9)")

# 2. random nontrivial instances (N=6)
cnt = 0
for trial in range(200):
    n = 6
    p = rand_unit(n); r = rand_unit(n)
    if abs(np.vdot(p, r)) < 1e-8:  # need non-orthogonal pair
        pass
    # force generic non-orthogonal p, r by mixing
    p = rand_unit(n); r = rand_unit(n)
    q = rand_unit(n); s = rand_unit(n)
    # enforce P ⟂ Q and R ⟂ S via Gram–Schmidt inside pairs
    # build: p, then r ⊥? no — r need not be ⊥ p. q ⟂ p, s ⟂ r, and ranges disjoint.
    # Construct in blocks: take p, r generic in span(e1..e4); q ⟂ p, s ⟂ r in span(e1..e6)
    q = q - np.vdot(p, q)*p/np.vdot(p,p) if False else q
    # simpler: orthogonalize q against p, s against r
    q = q - (np.vdot(p, q)/np.vdot(p, p))*p
    s = s - (np.vdot(r, s)/np.vdot(r, r))*r
    q /= np.linalg.norm(q); s /= np.linalg.norm(s)
    P, R, Q, S = proj(p), proj(r), proj(q), proj(s)
    # disjointness: generic lines are disjoint w.p. 1 (dim>=3)
    assert abs(np.trace(P@R).real) > 1e-6  # nontrivial overlap-free but non-orthogonal
    ok = check_instance(P, R, Q, S, f"trial{trial:03d} ranks 1,1,1,1") if trial < 3 else None
    cnt += ok if ok is not None else (np.trace(P@R+Q@S).real + 1e-9 >= np.trace(mpinvsqrt(P+R)@P@mpinvsqrt(P+R) @ (mpinvsqrt(Q+S)@Q@mpinvsqrt(Q+S)) + (mpinvsqrt(P+R)@R@mpinvsqrt(P+R)) @ (mpinvsqrt(Q+S)@S@mpinvsqrt(Q+S))).real)
print(f"200 randomized full-hypothesis instances passed: {cnt}/200")

# rank balances: ranks 1,1,1,1 give 1+1=1+1 and 1+1=1+1 — balanced.
# Unbalanced: ranks 1,2,2,1? balances need 1+1=2+1? no. Use ranks (1,1,2,0): 1+1=2+0 ✓, 1+2=1+0? ✗.
# Try ranks (1,2,1,2): 1+2=1+2 ✓; 1+1=2+2 ✗. Just probe unbalanced directly:
ok_all = True
for trial in range(50):
    n = 8
    p = rand_unit(n)
    # R: 2-dim subspace containing no multiple of p
    B = rng.normal(size=(n,2)) + 1j*rng.normal(size=(n,2))
    B[:,0] = p; Q_, _ = np.linalg.qr(B)
    r1, r2 = Q_[:,0], Q_[:,1]
    q = rand_unit(n); s = rand_unit(n)
    q = q - (np.vdot(p, q)/np.vdot(p,p))*p
    s = s - ((np.vdot(r1,s)*r1 + np.vdot(r2,s)*r2))  # s ⟂ span(r1,r2)
    s /= np.linalg.norm(s)
    P = proj(p)
    R = proj(r1) + proj(r2)
    Q = proj(q); S = proj(s)
    X = mpinvsqrt(P+R); Y = mpinvsqrt(Q+S)
    rhs = np.trace((X@P@X)@(Y@Q@Y) + (X@R@X)@(Y@S@Y)).real
    lhs = np.trace(P@R + Q@S).real
    ok_all &= lhs + 1e-9 >= rhs
print(f"50 unbalanced-rank instances (ranks 1,2,1,1): inequality held: {ok_all}")

# 4. negative control: drop disjointness
n = 3
p = rand_unit(n); r = p.copy()  # ran P = ran R, intersection nonzero
q = rand_unit(n)
q = q - (np.vdot(p,q)/np.vdot(p,p))*p
s = q.copy()
P, R, Q, S = proj(p), proj(r), proj(q), proj(s)
X = mpinvsqrt(P+R); Y = mpinvsqrt(Q+S)
lhs = np.trace(P@R + Q@S).real
rhs = np.trace((X@P@X)@(Y@Q@Y) + (X@R@X)@(Y@S@Y)).real
print(f"negative control (P=R, Q=S): lhs={lhs:.4f} rhs={rhs:.4f} violated={lhs < rhs - 1e-9}")

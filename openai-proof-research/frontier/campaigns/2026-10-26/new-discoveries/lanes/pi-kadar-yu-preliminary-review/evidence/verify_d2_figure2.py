#!/usr/bin/env python3
"""
d=2 adversarial check of parent-kadar-yu PROOF.md, using ONLY Figure 2 of
arXiv:2512.24535v1 (Gram matrix Gamma( Delta^8_{(6,(2,1))} ), 20x20, the
equal tuple (8,8) for l=1, lambda=(2,1), d=2) and the published Sec 3.29 data:

  C^(2,1) = (a-2)^3 a (a+2) (a+4),
  P_5^(2,1) = a^4 - 7 a^2 + 3,  P_6^(2,1) = a(a-1)(a+1)(a^2-7),
  P_4 (k=-1) := a P_5 - P_6 = a^3 - 4a.

Structure of Figure 2 (1-indexed): head-1 = 1..7 (attach e1 = 7),
tail-1 = 8..10 (3 vertices = 8-5), head-2 = 11..17 (attach e2 = 17),
tail-2 = 18..20. Cross-head couplings present (sqrt(3)/2, -1/2, ...).

Checks (parent's exact setup: freeze tail-1 at N=5, extend tail-2):
  (A) Gamma_(5,5) := Fig2 with both tails deleted is 14x14 head block;
      Gamma_(5,5+s) := Gamma_(5,5) + s-path at e2.
      det Gamma_(5,5) == C * P5^2 and det Gamma_(5,6) == C * P5 P6 (Prop 3.25).
  (B) monic gcd(det G(5,5), det G(5,6)) == published C (parent gcd step, d=2).
  (C) Krylov compression of A = -(const part) at e2: r = deg P_5 = 4;
      q_0 == P_5, q_{-1} == P_4; q_s == P_{5+s} for s=0..3 as direct charpolys.
  (D) Full printed 20x20: det Gamma_(8,8) == C * P8^2  (end-to-end).
  (E) squarefreeness P_4..P_8; exterior counts bounded by r, monotone.
"""
import sympy as sp

a = sp.symbols('a')
s3 = sp.sqrt(3)


def fig2():
    """Constant part (alpha -> 0) of Figure 2, 20x20, transcribed from the
    PDF page-22 render; asserted symmetric."""
    M = sp.zeros(20, 20)
    rows = [
        [0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 1, 0, 0, 1, 1, -sp.Rational(1, 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, -s3 / 2, 0, 0, 0],
        [1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [1, 0, 1, 1, 0, 1, -sp.Rational(1, 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, s3 / 2, 0, 0, 0],
        [0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, -sp.Rational(1, 2), 0, -sp.Rational(1, 2), 1, 0, 1, 0, 0, 0, 0, s3 / 2, 0, s3 / 2, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, -1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, s3 / 2, 0, 0, 0, -1, 1, 0, 0, 1, -1, -sp.Rational(1, 2), 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0],
        [0, 0, 0, 0, 0, 0, s3 / 2, 0, 0, 0, -1, 0, 1, 1, 0, 1, sp.Rational(1, 2), 0, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 1, 0, 0, 0],
        [0, 0, -s3 / 2, 0, s3 / 2, 0, 0, 0, 0, 0, 0, 0, -sp.Rational(1, 2), 0, sp.Rational(1, 2), 1, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
        [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ]
    for i, r in enumerate(rows):
        for j, v in enumerate(r):
            M[i, j] = v
    assert M == M.T, "Figure 2 transcription not symmetric"
    return M


def drop(M, idxs):
    keep = [i for i in range(M.rows) if i not in idxs]
    return M[keep, keep]


def ext_path(A, e0, s):
    """A with an s-vertex zero-diagonal unit path appended at 0-indexed e0."""
    n = A.rows
    K = sp.Matrix(A)
    K = K.col_join(sp.zeros(s, n))
    K = K.row_join(sp.zeros(n + s, s))
    if s >= 1:
        K[e0, n] = 1
        K[n, e0] = 1
        for t in range(s - 1):
            K[n + t, n + t + 1] = 1
            K[n + t + 1, n + t] = 1
    return K


def krylov_J(A, e_idx):
    n = A.rows
    e = sp.zeros(n, 1)
    e[e_idx] = 1
    vecs = []
    w = sp.Matrix(e)
    for _ in range(n):
        for u in vecs:
            w = w - (u.T * w)[0] * u
        nrm2 = sp.simplify((w.T * w)[0])
        if nrm2 == 0:
            break
        v = sp.simplify(w / sp.sqrt(nrm2))
        vecs.append(v)
        w = A * v
    r = len(vecs)
    J = sp.zeros(r, r)
    for i in range(r):
        for j in range(r):
            J[i, j] = sp.simplify((vecs[i].T * (A * vecs[j]))[0])
    return J, r


# published data (Sec 3.29 of the source)
C_pub = sp.expand((a - 2)**3 * a * (a + 2) * (a + 4))
P5 = sp.expand(a**4 - 7 * a**2 + 3)
P6 = sp.expand(a * (a - 1) * (a + 1) * (a**2 - 7))
P4 = sp.expand(a * P5 - P6)
print("published C =", sp.factor(C_pub))
print("published P_4 =", sp.factor(P4), "(= a P5 - P6)")

F = fig2()
# (A) both tails frozen at N=5: delete tail-1 rows/cols {7,8,9} and
#     tail-2 rows/cols {17,18,19} (0-indexed)
G55_B = drop(F, {7, 8, 9, 17, 18, 19})   # 14x14 head block (alpha->0)
A55 = -G55_B                              # det Gamma_(5,5) = det(a I - A55)
# e2 (0-indexed 16 in the 20x20) shifts to 13 after dropping {7,8,9}
E2 = 16 - 3
# Gamma_(5,6): tail-2 extended by one vertex at e2
A56 = ext_path(A55, E2, 1)

detG55 = sp.factor(sp.Matrix(A55).charpoly(a).as_expr())
detG56 = sp.factor(sp.Matrix(A56).charpoly(a).as_expr())
print("det G(5,5) == C*P5^2 :",
      sp.simplify(sp.expand(detG55) - sp.expand(C_pub * P5**2)) == 0)
print("det G(5,6) == C*P5*P6:",
      sp.simplify(sp.expand(detG56) - sp.expand(C_pub * P5 * P6)) == 0)

# (B) gcd step: parent's F = C * P_N^(d-1) = C * P_5 for d=2
F_exp = sp.expand(C_pub * P5)
c = sp.monic(sp.gcd(sp.Poly(detG55, a), sp.Poly(detG56, a))).as_expr()
print("monic gcd(det G55, det G56) == C*P5 (= F):",
      sp.simplify(sp.expand(c - F_exp)) == 0, "| gcd =", sp.factor(c))

# (C) compression at e2 (index E2 = 13 in the 14x14)
J, r = krylov_J(A55, E2)
print("Krylov dim r =", r, "(== deg P_5 =", sp.degree(P5, a), ")")
offs = [J[i + 1, i] for i in range(r - 1)]
assert all(o != 0 for o in offs), "J reducible!"
for i in range(r):
    for j in range(r):
        if abs(i - j) > 1:
            assert J[i, j] == 0, f"J not tridiagonal at {i},{j}"
q0 = sp.expand(sp.Matrix(J).charpoly(a).as_expr())
Jm1 = J[1:r, 1:r]
qm1 = sp.expand(Jm1.charpoly(a).as_expr()) if r > 1 else sp.Integer(1)
print("q_0 == P_5 :", sp.simplify(q0 - P5) == 0)
print("q_{-1} == P_4:", sp.simplify(qm1 - P4) == 0)

P = {4: P4, 5: P5, 6: P6}
for n in (7, 8):
    P[n] = sp.expand(a * P[n - 1] - P[n - 2])
ok = True
for s in range(0, 4):
    q = sp.expand(ext_path(J, 0, s).charpoly(a).as_expr())
    ok &= sp.simplify(q - P[5 + s]) == 0
print("q_s == P_{5+s} for s=0..3 (direct charpolys):", ok)

# (D) full printed 20x20: Gamma_(8,8) constant part = -F; det = C*P8^2
detG88 = sp.factor(sp.Matrix(-F).charpoly(a).as_expr())
ok = sp.simplify(sp.expand(detG88) - sp.expand(C_pub * P[8]**2)) == 0
print("det Gamma_(8,8) (full Fig2) == C * P_8^2:", ok)

# (E) squarefree + exterior counts
sq = all(sp.gcd(sp.Poly(P[n], a), sp.Poly(sp.diff(P[n], a), a)).degree() == 0
         for n in range(4, 9))
print("P_4..P_8 squarefree:", sq)
ext = []
for n in range(4, 9):
    rr = [complex(z) for z in sp.nroots(sp.Poly(P[n], a), n=25, maxsteps=300)]
    ext.append(sum(1 for z in rr if abs(z) > 2 + 1e-9))
print("exterior counts n=4..8:", ext, "| bounded by r =", r, ":", max(ext) <= r)
print("ALL d=2 CHECKS COMPLETE")

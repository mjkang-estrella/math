#!/usr/bin/env python3
"""
Independent adversarial check of parent-kadar-yu PROOF.md sections 2-3,
using ONLY data printed in arXiv:2512.24535v1:

  - Eq (3.2.5): the full 15x15 Gram matrix of Delta^{(11,(3))} (eps=+1) and
    Delta^{(11,(1^3))} (eps=-1) for J_{1,13}; head = rows/cols 1..7,
    tail = 8 unit-weight, zero-(alpha-)diagonal vertices (rows/cols 8..15).
  - Sec 3.3: published C^(3) = (a-2)^2 a^2, P_5^(3) = (a+1)(a^2+3a-6),
    P_6^(3) = a(a^3+4a^2-4a-10);
             C^(1^3) = (a-2)^2 (a+2)^3, P_5^(1^3) = a^2-2a-3,
    P_6^(1^3) = a^3-2a^2-4a+2.
  - Remark 3.33: P_4^(3) = a(a+4), P_4^(1^3) = a-2 (k=-1 boundary).

Checks performed (parent's chain replicated from scratch):
  (A) det Gamma_5 = charpoly of 7x7 head; det Gamma_6 = charpoly of head+1 tail
      vertex. monic gcd(det Gamma_5, det Gamma_6) == published C (parent Sec 3
      gcd step) and the quotients == published P_5, P_6 (parent identification).
  (B) Exact Krylov compression of A = -B_head at e = coordinate 7 (the tail
      attach point): J irreducible tridiagonal r x r; q_{-1} (delete e) == P_4
      (k=-1 claim); q_s (J with s-path at e) == P_{5+s} for s = 0..8.
  (C) det Gamma_(13) (full 15x15) == C * q_8 == C * P_13 (Prop 3.25 + Sec 3).
  (D) exterior-root counts h_s^+-, monotone, bounded by r; density grid check.
"""
import sympy as sp

a = sp.symbols('a')


def head(eps):
    """Constant part B_head (alpha -> 0) of Eq (3.2.5), rows/cols 1..7."""
    B = sp.zeros(7, 7)
    rows = [
        [0, 1, eps, 1, eps, 0, 0],
        [1, 0, 1, 1, 0, eps, 0],
        [eps, 1, 0, 0, 1, eps, 1],
        [1, 1, 0, 0, 1, 1, 0],
        [eps, 0, 1, 1, 0, 1, eps],
        [0, eps, eps, 1, 1, 0, 1],
        [0, 0, 1, 0, eps, 1, 0],
    ]
    for i, r in enumerate(rows):
        for j, v in enumerate(r):
            B[i, j] = sp.Integer(v)
    assert B == B.T, "head not symmetric"
    return B


def extended(B, s):
    """A = -B with an s-vertex unit path appended at coordinate 7 (1-indexed)."""
    n = B.rows
    A = -sp.Matrix(B)
    A = A.col_join(sp.zeros(s, n))
    A = A.row_join(sp.zeros(n + s, s))
    if s >= 1:
        A[6, n] = 1   # coupling e (coord 7) to first new vertex, weight 1
        A[n, 6] = 1
        for k in range(s - 1):
            A[n + k, n + k + 1] = 1
            A[n + k + 1, n + k] = 1
    return A


def krylov_J(A, e_idx):
    """Exact Krylov compression: orthonormalize {e, Ae, A^2 e, ...} with full
    reorthogonalization (exact arithmetic). Returns (J, r) with J the r x r
    Jacobi matrix of K in the v_1 = e ordering (e at position 1)."""
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


def J_with_path(J, s):
    """J with an s-vertex zero-diagonal unit path appended at position 0 (e)."""
    m = J.rows
    K = sp.Matrix(J)
    K = K.col_join(sp.zeros(s, m))
    K = K.row_join(sp.zeros(m + s, s))
    if s >= 1:
        K[0, m] = 1
        K[m, 0] = 1
        for t in range(s - 1):
            K[m + t, m + t + 1] = 1
            K[m + t + 1, m + t] = 1
    return K


def check(eps, C_pub, P5_pub, P6_pub, P4_pub, label):
    print(f"=== eps = {eps:+d}  ({label}) ===")
    B = head(eps)
    A5 = extended(B, 0)          # 7x7, Gamma_(5) constant part
    A6 = extended(B, 1)          # 8x8
    A15 = extended(B, 8)         # 15x15, Gamma_(13)

    # (A) charpolys in alpha: det(alpha*I - A)
    detG5 = sp.factor(sp.Matrix(A5).charpoly(a).as_expr())
    detG6 = sp.factor(sp.Matrix(A6).charpoly(a).as_expr())
    c = sp.monic(sp.gcd(sp.Poly(detG5, a), sp.Poly(detG6, a))).as_expr()
    print("monic gcd(det G5, det G6) =", c)
    print("  published C              =", sp.factor(C_pub),
          "-> match:", sp.simplify(sp.expand(c - C_pub)) == 0)

    Ph5 = sp.cancel(sp.expand(detG5 / c))
    Ph6 = sp.cancel(sp.expand(detG6 / c))
    print("derived P_5 =", sp.factor(Ph5), " match:",
          sp.simplify(Ph5 - P5_pub) == 0)
    print("derived P_6 =", sp.factor(Ph6), " match:",
          sp.simplify(Ph6 - P6_pub) == 0)

    # (B) compression
    J, r = krylov_J(sp.Matrix(-B), 6)
    print("Krylov dim r =", r, " (== deg P_5 =", sp.degree(P5_pub, a), ")")
    offs = [J[i + 1, i] for i in range(r - 1)]
    assert all(o != 0 for o in offs), "J reducible!"
    for i in range(r):
        for j in range(r):
            if abs(i - j) > 1:
                assert J[i, j] == 0, f"J not tridiagonal at {i},{j}"
    q0 = sp.expand(sp.Matrix(J).charpoly(a).as_expr())
    Jm1 = J[1:r, 1:r]   # delete e (position 1 in v-ordering)
    qm1 = sp.expand(Jm1.charpoly(a).as_expr()) if r > 1 else sp.Integer(1)
    print("q_0    =", sp.factor(q0), " == P_5:", sp.simplify(q0 - P5_pub) == 0)
    print("q_{-1} =", sp.factor(qm1), " == P_4:",
          sp.simplify(qm1 - P4_pub) == 0,
          "| == x*P5-P6:", sp.simplify(qm1 - (a * P5_pub - P6_pub)) == 0)

    # q_s for s = 0..8 directly as charpolys of J_s (independent of recursion)
    qs = []
    P = {4: P4_pub, 5: P5_pub, 6: P6_pub}
    for n in range(7, 14):
        P[n] = sp.expand(a * P[n - 1] - P[n - 2])
    allmatch = True
    for s in range(0, 9):
        q = sp.expand(J_with_path(J, s).charpoly(a).as_expr())
        ok = sp.simplify(q - P[5 + s]) == 0
        allmatch &= ok
        if not ok:
            print(f"  MISMATCH s={s}: q_s={sp.factor(q)} vs P={sp.factor(P[5+s])}")
    print("q_s == P_{5+s} for s=0..8 (direct charpolys):", allmatch)

    # strict interlacing q_0 vs q_1: disjoint roots, and interlacing order
    r0 = sorted(sp.nroots(sp.Poly(q0, a)), key=sp.re)
    r1 = sorted(sp.nroots(sp.Poly(P[6], a)), key=sp.re)
    disjoint = all(abs(complex(x) - complex(y)) > 1e-8 for x in r0 for y in r1)
    inter = all(r1[i] < r0[i] < r1[i + 1] for i in range(len(r0)))
    print("q_0, q_1 disjoint:", disjoint, "| strictly interlaced:", inter)

    # (C) full 15x15 determinant
    detG13 = sp.factor(sp.Matrix(A15).charpoly(a).as_expr())
    ok = sp.simplify(sp.expand(detG13) - sp.expand(C_pub * P[13])) == 0
    print("det Gamma_(13) == C * P_13:", ok)

    # (D) squarefreeness P_4..P_13 and exterior counts bounded by r
    sq = all(sp.gcd(sp.Poly(P[n], a), sp.Poly(sp.diff(P[n], a), a)).degree() == 0
             for n in range(4, 14))
    print("P_4..P_13 squarefree:", sq)
    ext = []
    for n in range(4, 14):
        rr = [complex(z) for z in sp.nroots(sp.Poly(P[n], a), n=25, maxsteps=200)]
        ext.append(sum(1 for z in rr if abs(z) > 2 + 1e-9))
    print("exterior counts |root|>2, n=4..13:", ext)
    print("monotone nondecreasing:", all(ext[i] <= ext[i + 1] for i in range(len(ext) - 1)),
          "| bounded by r =", r, ":", max(ext) <= r)
    print()
    return True


# Published data from arXiv:2512.24535v1, Sec 3.3 and Remark 3.33
check(+1, (a - 2)**2 * a**2,
      sp.expand((a + 1) * (a**2 + 3 * a - 6)),
      sp.expand(a * (a**3 + 4 * a**2 - 4 * a - 10)),
      sp.expand(a * (a + 4)), "lambda=(3)")
check(-1, (a - 2)**2 * (a + 2)**3,
      sp.expand(a**2 - 2 * a - 3),
      sp.expand(a**3 - 2 * a**2 - 4 * a + 2),
      sp.expand(a - 2), "lambda=(1^3)")
print("ALL CHECKS COMPLETE")

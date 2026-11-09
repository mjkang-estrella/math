#!/usr/bin/env python3
# MIT License. Author: Myeongjin Kang. Float control (NOT a proof): compares, for random 4-polytopes with 6
# facets, the directly computed P_4(K) = V(Pi K)/V(K)^3 with the reduction formula of Proposition A in proof.md,
# and checks P_4(K) < 160/3. Also computes P_4 of a random simplex (expected 160/3). Pure Python, deterministic.
import sys
import math
import random
import itertools

sys.dont_write_bytecode = True
N = 4
C4 = (N + 1) * N ** N / math.factorial(N)  # 160/3


def det(M):
    M = [row[:] for row in M]
    n = len(M)
    d = 1.0
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if abs(M[p][c]) < 1e-300:
            return 0.0
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for cc in range(c, n):
                M[r][cc] -= f * M[c][cc]
    return d


def solve(A, b):
    n = len(A)
    M = [A[i][:] + [b[i]] for i in range(n)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        if abs(M[p][c]) < 1e-12:
            return None
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                for cc in range(c, n + 1):
                    M[r][cc] -= f * M[c][cc]
    return [M[i][n] / M[i][i] for i in range(n)]


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def gs(vecs):
    basis = []
    for v in vecs:
        w = v[:]
        for e in basis:
            c = dot(w, e)
            w = [x - c * y for x, y in zip(w, e)]
        nr = math.sqrt(dot(w, w))
        if nr > 1e-9:
            basis.append([x / nr for x in w])
    return basis


def polytope(U, h):
    m = len(U)
    verts = []
    for S in itertools.combinations(range(m), N):
        x = solve([U[i] for i in S], [h[i] for i in S])
        if x is None:
            continue
        if all(dot(U[i], x) <= h[i] + 1e-9 for i in range(m)):
            if not any(max(abs(a - b) for a, b in zip(x, y)) < 1e-9 for y in verts):
                verts.append(x)
    tight = [frozenset(i for i in range(m) if abs(dot(U[i], v) - h[i]) < 1e-9) for v in verts]
    return verts, tight


def face_volume(vidx, verts, tight, d, m):
    """vidx: tuple of vertex indices of a d-dimensional face."""
    pts = [verts[i] for i in vidx]
    if d == 1:
        return max(math.sqrt(dot(sub(p, q), sub(p, q))) for p in pts for q in pts)
    c = [sum(col) / len(pts) for col in zip(*pts)]
    total = 0.0
    seen = set()
    common = frozenset.intersection(*[tight[i] for i in vidx])
    for j in range(m):
        if j in common:
            continue
        sv = tuple(i for i in vidx if j in tight[i])
        if len(sv) < d or sv in seen:
            continue
        B = gs([sub(verts[i], verts[sv[0]]) for i in sv[1:]])
        if len(B) != d - 1:
            continue
        seen.add(sv)
        r = sub(c, verts[sv[0]])
        for e in B:
            cc = dot(r, e)
            r = [x - cc * y for x, y in zip(r, e)]
        total += math.sqrt(dot(r, r)) * face_volume(sv, verts, tight, d - 1, m) / d
    return total


def direct_P(U, h):
    m = len(U)
    verts, tight = polytope(U, h)
    V = face_volume(tuple(range(len(verts))), verts, tight, N, m)
    f = []
    for i in range(m):
        vi = tuple(k for k in range(len(verts)) if i in tight[k])
        B = gs([sub(verts[k], verts[vi[0]]) for k in vi[1:]]) if vi else []
        f.append(face_volume(vi, verts, tight, N - 1, m) if len(B) == N - 1 else 0.0)
    w = [[f[i] * x for x in U[i]] for i in range(m)]
    PiK = sum(abs(det([w[j] for j in J])) for J in itertools.combinations(range(m), N))
    mink = sum(h[i] * f[i] for i in range(m)) / N
    return PiK / V ** (N - 1), V, mink, f, w


def nullvec(w):
    """vector a orthogonal to 1 with sum_i a_i w_i = 0 (6 vectors in R^4)."""
    m = len(w)
    # rows: 4 coordinate equations + sum a_i = 0 ; 5 equations, 6 unknowns; fix a_m = 1 then solve 5x5
    A = [[w[i][r] for i in range(m - 1)] for r in range(N)] + [[1.0] * (m - 1)]
    b = [-w[m - 1][r] for r in range(N)] + [-1.0]
    x = solve(A, b)
    return x + [1.0]


def fY0(c):
    """density at 0 of sum c_i E_i (distinct nonzero c, both signs present), partial fractions."""
    s = 0.0
    for j, cj in enumerate(c):
        if cj > 0:
            A = 1.0
            for i, ci in enumerate(c):
                if i != j:
                    A *= cj / (cj - ci)
            s += A / cj
    return s


def formula_ratio(a, t):
    D = sum(abs(x - y) for x, y in itertools.combinations(a, 2))
    return D * fY0([x - t for x in a]) / (N + 1)


def main():
    rng = random.Random(4061)
    ok = True
    # simplex control
    S = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [-1, -1, -1, -1]]
    M = [[rng.uniform(-1, 1) for _ in range(N)] for _ in range(N)]
    U = [[dot(M[r], s) for r in range(N)] for s in S]
    U = [[x / math.sqrt(dot(u, u)) for x in u] for u in U]
    Ps, _, _, _, _ = direct_P(U, [rng.uniform(0.5, 1.5) for _ in range(5)])
    print("simplex: P_4 = %.10f, 160/3 = %.10f" % (Ps, C4))
    ok &= abs(Ps / C4 - 1) < 1e-9
    worst = 0.0
    done = 0
    while done < 40:
        M = [[rng.uniform(-1, 1) for _ in range(N)] for _ in range(N)]
        U = [[dot(M[r], s) for r in range(N)] for s in S] + [[rng.gauss(0, 1) for _ in range(N)]]
        U = [[x / math.sqrt(dot(u, u)) for x in u] for u in U]
        h = [rng.uniform(0.5, 1.5) for _ in range(6)]
        if abs(det(M)) < 0.05:
            continue
        P, V, mink, f, w = direct_P(U, h)
        if min(f) < 1e-6 * max(f):
            continue  # a redundant inequality: fewer than 6 facets
        a = nullvec(w)
        lam = [f[i] * h[i] for i in range(6)]
        sl = sum(lam)
        tstar = sum(ai * li for ai, li in zip(a, lam)) / sl
        rf = formula_ratio(a, tstar)
        lo, hi = min(a), max(a)
        grid = max(formula_ratio(a, lo + (hi - lo) * (k + 0.5) / 400) for k in range(400))
        good = abs(mink / V - 1) < 1e-8 and abs(rf - P / C4) < 1e-8 and grid <= rf + 1e-9 and P < C4
        ok &= good
        worst = max(worst, P / C4)
        done += 1
        if done <= 5 or not good:
            print("6 facets: P/c4 direct %.10f  formula(t*) %.10f  max_grid %.10f  Minkowski %.2e %s"
                  % (P / C4, rf, grid, abs(mink / V - 1), "OK" if good else "FAIL"))
    print("40 random 6-facet 4-polytopes: max P_4/c_4 = %.6f" % worst)
    print("GEOMETRY CONTROL", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())

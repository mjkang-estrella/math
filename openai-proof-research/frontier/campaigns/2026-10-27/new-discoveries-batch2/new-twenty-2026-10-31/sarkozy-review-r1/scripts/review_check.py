#!/usr/bin/env python3
"""Independent review checks for MathDB 353800 (sarkozy-review-r1).

Written from scratch by the reviewer; imports nothing from the discovery lane.
Usage: python3 -I review_check.py <part> [args]
Parts:
  q5n4            rebuild X and A at (q,k,n) = (5,2,4) from the dossier's DEFINITION, compare with
                  the dossier listing (passed as a literal below), full polynomial square test.
  unif <q>        Theorem U at q (prime power, q = 1 mod 4): build X_q, check size formula,
                  check independence in F_q^3, and full polynomial check of A = X_q x F_q at n = 4.
  win58           Theorem 3 with r = 1, q = 5, n = 8: build A (20000 polys) and test all u + b^2.
  slice <q> <r> <json> <key>  Theorem 3 with m = r on a slice read as DATA from a JSON file.
  hoffman <p>     Hoffman ratio bound for the slice graph at a prime p (any residue mod 4).
"""
import sys, itertools, json, math, cmath, time

# ---------------- finite field GF(p^e), elements encoded as ints 0..q-1 ----------------

def make_field(q):
    p = None
    for c in range(2, q + 1):
        if q % c == 0:
            p = c
            break
    e = 0
    t = q
    while t % p == 0:
        t //= p
        e += 1
    assert t == 1, "q must be a prime power"
    if e == 1:
        add = [[(a + b) % p for b in range(q)] for a in range(q)]
        mul = [[(a * b) % p for b in range(q)] for a in range(q)]
        return p, add, mul
    # search a monic modulus of degree e making the multiplication table a field
    def digits(x):
        return [(x // p ** i) % p for i in range(e)]
    def undig(d):
        return sum(d[i] * p ** i for i in range(e))
    add = [[undig([(x + y) % p for x, y in zip(digits(a), digits(b))]) for b in range(q)] for a in range(q)]
    for tail in itertools.product(range(p), repeat=e):
        if tail[0] == 0:
            continue
        def pm(a, b):
            da, db = digits(a), digits(b)
            prod = [0] * (2 * e - 1)
            for i in range(e):
                for j in range(e):
                    prod[i + j] = (prod[i + j] + da[i] * db[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                c = prod[k]
                if c:
                    prod[k] = 0
                    for i in range(e):  # x^e = -(tail)
                        prod[k - e + i] = (prod[k - e + i] - c * tail[i]) % p
            return undig(prod[:e])
        mul = [[pm(a, b) for b in range(q)] for a in range(q)]
        # field test: every nonzero element has an inverse
        if all(any(mul[a][b] == 1 for b in range(1, q)) for a in range(1, q)):
            return p, add, mul
    raise RuntimeError("no modulus found")

class Field:
    def __init__(self, q):
        self.q = q
        self.p, self.A, self.M = make_field(q)
        self.neg = [next(b for b in range(q) if self.A[a][b] == 0) for a in range(q)]
        self.sq = set(self.M[a][a] for a in range(1, q))  # nonzero squares
        assert len(self.sq) == (q - 1) // 2 if q % 2 else True
    def add(self, a, b): return self.A[a][b]
    def sub(self, a, b): return self.A[a][self.neg[b]]
    def mul(self, a, b): return self.M[a][b]
    def c(self, n):  # image of the integer n
        n %= self.p
        r = 0
        for _ in range(n):
            r = self.A[r][1]
        return r

# ---------------- polynomials as coefficient tuples (low -> high) ----------------

def poly_mul(F, a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if y:
                out[i + j] = F.add(out[i + j], F.mul(x, y))
    return out

def deg(v):
    for i in range(len(v) - 1, -1, -1):
        if v[i]:
            return i
    return -1

def nonzero_squares_below(F, n):
    """All nonzero b^2 with deg(b^2) < n, b ranging over ALL of P_{q,n} (a superset of what is
    needed: if deg b >= n/2 then deg b^2 >= n). Returns dict square-vector -> list of b."""
    out = {}
    for b in itertools.product(range(F.q), repeat=n):
        if deg(b) < 0:
            continue
        s = poly_mul(F, b, b)
        if deg(s) < n:
            v = tuple((s + [0] * n)[:n])
            out.setdefault(v, []).append(b)
    return out

def check_family(F, A, n, label):
    """A: set of n-tuples. Returns number of (u, d) with u in A, d a nonzero square, u + d in A."""
    t0 = time.time()
    sqs = nonzero_squares_below(F, n)
    viol = 0
    for u in A:
        for d in sqs:
            w = tuple(F.add(x, y) for x, y in zip(u, d))
            if w in A:
                viol += 1
    print(f"[{label}] |A| = {len(A)}, distinct nonzero squares of degree < {n}: {len(sqs)}, "
          f"b values giving them: {sum(len(v) for v in sqs.values())}, violations u + b^2 in A: {viol}, "
          f"{time.time() - t0:.1f}s")
    return viol, sqs

# ---------------- the slice objects ----------------

def D(F, v):  # 4xz - y^2
    x, y, z = v
    return F.sub(F.mul(F.c(4), F.mul(x, z)), F.mul(y, y))

def Svec(F):
    return {(F.mul(a, a), F.mul(F.c(2), F.mul(a, b)), F.mul(b, b))
            for a in range(F.q) for b in range(F.q) if (a, b) != (0, 0)}

def pg1_reps(F):
    return [(1, b) for b in range(F.q)] + [(0, 1)]

def greedy_I(F):
    I = []
    for t in sorted(F.sq):
        if all(F.sub(t, s) not in F.sq for s in I):  # distinct squares, difference never a square
            I.append(t)
    return I

def theoremU_X(F, c=None, I=None):
    q = F.q
    if c is None:
        c = min(x for x in range(1, q) if x not in F.sq)  # a nonsquare
    assert c not in F.sq and c != 0
    if I is None:
        I = greedy_I(F)
    L = {(x, y, z) for x in range(q) for y in range(q) for z in range(q) if D(F, (x, y, z)) == c}
    added = set()
    for (a, b) in pg1_reps(F):
        rep = (F.mul(a, a), F.mul(F.c(2), F.mul(a, b)), F.mul(b, b))
        for t in I:
            added.add(tuple(F.mul(t, r) for r in rep))
    assert not (L & added)
    return L | added, L, added, c, I

def slice_independent(F, X):
    S = Svec(F)
    bad = 0
    for x in X:
        for s in S:
            if tuple(F.add(a, b) for a, b in zip(x, s)) in X:
                bad += 1
    return bad, len(S)

# ---------------- parts ----------------

DOSSIER_LISTING = [
    (0,0,1),(0,0,4),(1,0,0),(1,0,3),(1,1,2),(1,1,4),(1,2,1),(1,2,4),(1,3,1),(1,3,4),(1,4,2),(1,4,4),
    (2,0,4),(2,1,1),(2,2,2),(2,3,2),(2,4,1),(3,0,1),(3,1,4),(3,2,3),(3,3,3),(3,4,4),(4,0,0),(4,0,2),
    (4,1,1),(4,1,3),(4,2,1),(4,2,4),(4,3,1),(4,3,4),(4,4,1),(4,4,3)]

def part_q5n4():
    F = Field(5)
    X, L, added, c, I = theoremU_X(F, c=2, I=[1, 4])
    print("q = 5: c =", c, "I =", I, "|L| =", len(L), "|added| =", len(added), "|X| =", len(X))
    print("added points equal the full set S of 12 nonzero square vectors:", added == Svec(F), len(Svec(F)))
    lst = DOSSIER_LISTING
    print("dossier listing: length", len(lst), "distinct", len(set(lst)), "equals rebuilt X:", set(lst) == X)
    print("0 in X:", (0, 0, 0) in X)
    bad, nS = slice_independent(F, X)
    print("slice check: |S| =", nS, "violations x + s in X:", bad)
    A = {x + (c3,) for x in X for c3 in range(5)}
    print("|A| =", len(A), " bound 5^(4*(1-1/4)) =", 5 ** 3)
    # full ordered-pair test against an explicit list of ALL squares of degree < 4
    sqs = nonzero_squares_below(F, 4)
    blist = sorted({b for v in sqs.values() for b in v})
    print("b in P_{5,4} with 0 < deg(b^2) < 4 or b^2 nonzero const: count", len(blist),
          "max deg b:", max(deg(b) for b in blist), "(Lemma 1 predicts 24 nonzero b of degree <= 1)")
    print("distinct nonzero squares of degree < 4:", len(sqs), "(12 predicted; with 0 that is 13 values from 25 b)")
    sqset = set(sqs)
    Al = sorted(A)
    pairs = 0
    viol = 0
    for u in Al:
        for v in Al:
            if u == v:
                continue
            pairs += 1
            if tuple(F.sub(a, b) for a, b in zip(u, v)) in sqset:
                viol += 1
    print("ordered pairs tested:", pairs, "square differences found:", viol)
    # also confirm each coefficient vector of (b0 + b1 T)^2 is (b0^2, 2 b0 b1, b1^2, 0)
    ok = all(v == (F.mul(b[0], b[0]), F.mul(2, F.mul(b[0], b[1])), F.mul(b[1], b[1]), 0)
             for v, bs in sqs.items() for b in bs)
    print("Lemma 1 coefficient form confirmed on all square-producing b:", ok)
    print("RESULT q5n4:", "COUNTEREXAMPLE" if viol == 0 and len(A) == 160 and 160 > 125 else "FAIL")

def part_unif(q):
    F = Field(q)
    assert q % 4 == 1
    X, L, added, c, I = theoremU_X(F)
    formula = q * q - q + (q + 1) * len(I)
    print(f"q = {q} (p = {F.p}): nonsquare c = {c}, greedy I = {I} (|I| = {len(I)}), |L| = {len(L)} "
          f"(q(q-1) = {q*(q-1)}), |X_q| = {len(X)}, formula q^2 - q + (q+1)|I| = {formula}, > q^2 = {q*q}: {len(X) > q*q}")
    # I property check
    okI = all(F.sub(s, t) not in F.sq for s in I for t in I if s != t) and all(t in F.sq for t in I)
    print("I is a set of nonzero squares with no square difference:", okI)
    bad, nS = slice_independent(F, X)
    print(f"slice check: |S| = {nS}, violations: {bad}")
    if q ** 4 <= 30000:
        A = {x + (c3,) for x in X for c3 in range(q)}
        viol, sqs = check_family(F, A, 4, f"Theorem U full polynomial check q = {q}, n = 4")
        print(f"RESULT unif q = {q}: |A| = {len(A)} vs q^3 = {q**3}; violations {viol}")
    else:
        print(f"RESULT unif q = {q}: slice-level only; |A| = q|X| = {q*len(X)} vs q^3 = {q**3}")

def part_win58():
    F = Field(5)
    X, _, _, _, _ = theoremU_X(F, c=2, I=[1, 4])
    beta = 2  # nonsquare mod 5
    U = [(t, F.mul(beta, t)) for t in range(5)]
    n, m, r = 8, 2, 1
    W = list(range(2 * m - 2 * r, 2 * m + 2 * r - 1))  # [2,4]
    pairs = [(i, n - 2 - i) for i in range(0, 2 * m - 2 * r - 1, 2)]  # [(0,6)]
    used = set(W) | {i for pr in pairs for i in pr}
    free = [i for i in range(n) if i not in used]
    print("W =", W, "pairs =", pairs, "free =", free)
    assert all(i % 2 == 1 for i in free)
    A = set()
    for x in X:
        for (u0, u1) in U:
            for fr in itertools.product(range(5), repeat=len(free)):
                v = [None] * n
                for i, val in zip(W, x):
                    v[i] = val
                (i0, i1), = pairs
                v[i0], v[i1] = u0, u1
                for i, val in zip(free, fr):
                    v[i] = val
                A.add(tuple(v))
    print("|A| =", len(A), "formula q^(3(m-r)+1)|X| =", 5 ** (3 * (m - r) + 1) * len(X), " vs 5^6 =", 5 ** 6)
    viol, _ = check_family(F, A, 8, "Theorem 3 q = 5, n = 8, r = 1")
    print("RESULT win58:", "OK" if viol == 0 and len(A) > 5 ** 6 else "FAIL")

def part_slice(q, r, path, key):
    F = Field(q)
    with open(path) as fh:
        data = json.load(fh)
    X = data
    for k in key.split("."):
        if k:
            X = X[int(k)] if isinstance(X, list) else X[k]
    X = {tuple(int(c) for c in x) for x in X}
    dim = 4 * r - 1
    assert all(len(x) == dim and all(0 <= c < q for c in x) for x in X)
    # Theorem 3 with m = r: W = [0, 4r - 2], position 4r - 1 free
    n = 4 * r
    A = {x + (c,) for x in X for c in range(q)}
    viol, _ = check_family(F, A, n, f"slice data q = {q}, r = {r}, n = {n}")
    print(f"RESULT slice q = {q}, r = {r}: |X| = {len(X)}, |A| = {len(A)} vs q^(3n/4) = {q ** (3 * r)}; violations {viol}")

def part_hoffman(p):
    F = Field(p)
    S = Svec(F)
    conn = S | {tuple(F.neg[a] for a in s) for s in S}
    w = cmath.exp(2j * math.pi / p)
    eig = []
    for chi in itertools.product(range(p), repeat=3):
        val = sum(w ** ((chi[0] * s[0] + chi[1] * s[1] + chi[2] * s[2]) % p) for s in conn)
        eig.append(val.real)
    dgr = len(conn)
    lmin = min(eig)
    hb = p ** 3 * (-lmin) / (dgr - lmin)
    print(f"p = {p}: |S u -S| = {dgr}, min eigenvalue {lmin:.6f}, Hoffman bound {hb:.6f}, p^2 = {p*p}")

if __name__ == "__main__":
    part = sys.argv[1]
    if part == "q5n4":
        part_q5n4()
    elif part == "unif":
        part_unif(int(sys.argv[2]))
    elif part == "win58":
        part_win58()
    elif part == "slice":
        part_slice(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5] if len(sys.argv) > 5 else "")
    elif part == "hoffman":
        part_hoffman(int(sys.argv[2]))

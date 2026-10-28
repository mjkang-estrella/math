"""Slot-3 independent recheck (different route: pure-dict Laurent algebra, no sympy).

Route A: literal enumeration of weak tuples and of tuples for s_{k,r}; compare
odd-moment sums directly for exponent 2k+1, k=0..6.
Route B: full Laurent-polynomial coefficient identity
   C(z)-C(1/z) == H(A+)-H(A-)   and   (3) C == z/(1-z)(T(A-)-z^n T(A+))
checked coefficient-wise by exact dict arithmetic after clearing denominators.
Bounded: n in 1..4, j in 1..5, largest tuple count binom(24,5)=42504.
"""
from collections import Counter
from itertools import combinations_with_replacement, product
from math import comb
from fractions import Fraction
import json

def polymul(a, b):  # dicts exp->int
    out = Counter()
    for e1, c1 in a.items():
        for e2, c2 in b.items():
            out[e1 + e2] += c1 * c2
    return dict(out)

def polyadd(a, b):
    out = Counter(a)
    out.update(b)
    return {e: c for e, c in out.items() if c != 0}

def scale(a, s):
    return {e: s * c for e, c in a.items()}

def odd_part(a):
    return {e: c for e, c in a.items() if e % 2 == 1}

results = {"routeA": [], "routeB": [], "status": "PASS"}

for n in range(1, 5):
    for j in range(1, 6):
        M = j * (n + 1)
        # Route A: literal weak tuples -> S-tilde side moments
        tilde = Counter()
        for lam in combinations_with_replacement(range(1, j * n + 1), j):
            for i in range(j):
                tilde[lam[i] - i * n] += 1
        # s_{k,r} via literal tuples (independent of coefficient def C_{j,q})
        moments = []
        for k in range(7):
            lhs = sum(c * q ** (2 * k + 1) for q, c in tilde.items())
            rhs = 0
            for r in range(1, j + 1):
                for xs in product(range(1, n + 1), repeat=r):
                    rhs += comb(M, j - r) * sum(xs) ** (2 * k + 1)
            assert lhs == rhs, (n, j, k)
            moments.append(lhs == rhs)
        results["routeA"].append({"n": n, "j": j, "k0_6_all_match": all(moments)})

        # Route B: dict Laurent algebra.
        Ap = {q: 1 for q in range(1, n + 1)}          # A+
        Am = {-q: 1 for q in range(1, n + 1)}         # A-
        # H(A) = sum_{r=1}^j binom(M,j-r) A^r
        H = {}
        for r in range(1, j + 1):
            pw = {0: 1}
            for _ in range(r):
                pw = polymul(pw, Ap)
            H = polyadd(H, scale(pw, comb(M, j - r)))
        Hm = {}
        for r in range(1, j + 1):
            pw = {0: 1}
            for _ in range(r):
                pw = polymul(pw, Am)
            Hm = polyadd(Hm, scale(pw, comb(M, j - r)))
        # C from pointed subsets (independent reindex)
        C = {}
        for a in range(1, M):
            for h in range(j):
                if 0 <= a - 1 - h and j - 1 - h <= M - 1 - a and h >= 0:
                    e = a - h * (n + 1)
                    C[e] = C.get(e, 0) + comb(a - 1, h) * comb(M - 1 - a, j - 1 - h)
        Cinv = {-e: c for e, c in C.items()}
        # identity (1): C - Cinv == H - Hm
        lhs1 = polyadd(C, scale(Cinv, -1))
        rhs1 = polyadd(H, scale(Hm, -1))
        assert lhs1 == rhs1, ("id1", n, j)
        # identity (3): (1-z)*C - z*T(Am) + z^(n+1)*T(Ap) == 0
        T = {}
        for r in range(j):
            pw = {0: 1}
            for _ in range(r):
                pw = polymul(pw, Am)
            T = polyadd(T, scale(pw, comb(M - 1, j - 1 - r)))
        Tp = {}
        for r in range(j):
            pw = {0: 1}
            for _ in range(r):
                pw = polymul(pw, Ap)
            Tp = polyadd(Tp, scale(pw, comb(M - 1, j - 1 - r)))
        e3 = polyadd(scale(C, 1), scale(C, -1))  # (1-z)*C = C - z*C
        e3 = polyadd(e3, {e: -c for e, c in scale(C, 1).items()})  # careful: redo below
        # recompute cleanly: (1-z)*C = C - z*C
        zC = {e + 1: c for e, c in C.items()}
        e3 = polyadd(C, scale(zC, -1))
        zT = {e + 1: c for e, c in T.items()}
        zp1Tp = {e + n + 1: c for e, c in Tp.items()}
        e3 = polyadd(e3, scale(zT, -1))
        e3 = polyadd(e3, zp1Tp)
        assert e3 == {}, ("id3", n, j, e3)
        # cross-check: L[H(A+)] (all positive exponents) == S~ moment
        op = H
        for k in [0, 3, 6]:
            sB = sum(c * q ** (2 * k + 1) for q, c in op.items())
            sA = sum(c * q ** (2 * k + 1) for q, c in tilde.items())
            assert sB == sA, ("oddpart", n, j, k)
        results["routeB"].append({"n": n, "j": j, "id1": True, "id3": True})

# Edge: j=1, n=1, k=0 explicit sanity: S~_{0,1}(1) = {1^1} = 1 = S_{0,1}(1)
results["edge"] = "j=1,n=1: S~_{0,1}(1)={1}=S_{0,1}(1) OK"

(HERE := __import__("pathlib").Path(__file__).resolve().parent)
(HERE / "review-checks.json").write_text(json.dumps(results, indent=2) + "\n")
print("PASS routeA+routeB: 20 grids, moments k=0..6, full Laurent identities (1),(3) coefficientwise")

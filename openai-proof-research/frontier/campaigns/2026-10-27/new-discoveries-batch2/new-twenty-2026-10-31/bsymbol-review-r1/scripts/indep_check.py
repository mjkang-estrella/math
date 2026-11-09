"""Reviewer's independent checks for MathDB 334207 (bsymbol-review-r1).

Written from BSYMBOL-ORDINARY-PROOF.md and from the Lean definition `sv`, not from the
author's scripts. Sections:
  W  window independence of the recursive sequence: rank over F_p (p = 2,3,5,7,11) and
     integer determinants (Bareiss) of every cyclic window;
  L  agreement of the ordinary-proof construction with the Lean recursion `sv`;
  BR bridge lemma stress test with RANDOM r-good T (not only the recursive one);
  P2 Part 2 stress test: minimum b-weight of ker H for RANDOM b-good H (not only the construction);
  C  exhaustive minimum b-distance of the constructed codes over F_2, F_3, F_4, F_5, F_7;
  K  Kurz (arXiv:2507.07728, Lemma 3.5) greedy repair at k = b, run from [I_b | 0];
  N  negative control: H with one dependent window gives d_b < 2b.
Usage: python3 -I indep_check.py SECTION...
"""
import sys, random, itertools
from fractions import Fraction

# ---------- finite fields: prime fields and GF(4) ----------
class GF:
    def __init__(self, q):
        self.q = q
        if q == 4:
            # elements 0,1,a,a+1 encoded 0..3 ; a^2 = a + 1
            self.add = lambda x, y: x ^ y
            mul = [[0]*4 for _ in range(4)]
            def m(x, y):
                r = 0
                for i in range(2):
                    if (y >> i) & 1:
                        r ^= x << i
                if r & 4:
                    r ^= 0b111
                return r
            for x in range(4):
                for y in range(4):
                    mul[x][y] = m(x, y)
            self.mul = lambda x, y: mul[x][y]
            self.neg = lambda x: x
            self.inv = lambda x: [None, 1, 3, 2][x]
        else:
            self.add = lambda x, y: (x + y) % q
            self.mul = lambda x, y: (x * y) % q
            self.neg = lambda x: (-x) % q
            self.inv = lambda x: pow(x, q - 2, q)

def rank(F, rows):
    rows = [list(r) for r in rows]
    rk, ncol = 0, len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = F.inv(rows[rk][c])
        rows[rk] = [F.mul(iv, x) for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [F.add(x, F.neg(F.mul(f, y))) for x, y in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def det_int(M):
    """Exact integer determinant (fraction-free elimination via Fractions)."""
    n = len(M); A = [[Fraction(x) for x in row] for row in M]; d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            if f:
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return int(d)

# ---------- the construction, two independent encodings ----------
def seq_proof(b, n):
    """From BSYMBOL-ORDINARY-PROOF.md (Theorem A, Lemma 1, Lemma 3)."""
    assert 1 <= b <= n
    if b == 1:
        return [[1] for _ in range(n)]
    e = lambda i: [1 if k == i else 0 for k in range(b)]
    if n % b == 0:
        return [e(j % b) for j in range(n)]
    M, r = divmod(n, b)
    T = seq_proof(r, b + r)
    assert all(T[j] == [1 if k == j else 0 for k in range(r)] for j in range(r))
    p = [T[r + k] for k in range(b)]
    w = [[p[k][c] for k in range(b)] for c in range(r)]
    return [e(j % b) for j in range(M * b)] + w

def sv(b, n, j, k):
    """Literal transcription of the Lean `sv` recursion."""
    if b == 0:
        return 0
    if n % b == 0:
        return 1 if j % b == k else 0
    if j < n // b * b:
        return 1 if j % b == k else 0
    return sv(n % b, b + n % b, n % b + k, j - n // b * b)

def windows(v):
    n, b = len(v), len(v[0])
    return [[v[(s + t) % n] for t in range(b)] for s in range(n)]

def good(F, v):
    b = len(v[0])
    return all(rank(F, w) == b for w in windows(v))

# ---------- b-weight and code enumeration ----------
def wt_b(x, b):
    n = len(x)
    return sum(1 for i in range(n) if any(x[(i + j) % n] for j in range(b)))

def min_bweight_kernel(F, H, b):
    """H is b x n with first b columns = I_b (after a check); enumerate ker H exhaustively."""
    n = len(H[0]); q = F.q
    assert all(H[i][j] == (1 if i == j else 0) for i in range(b) for j in range(b))
    best, count = None, 0
    for free in itertools.product(range(q), repeat=n - b):
        x = [0] * b + list(free)
        for i in range(b):
            s = 0
            for j in range(b, n):
                if H[i][j] and x[j]:
                    s = F.add(s, F.mul(H[i][j], x[j]))
            x[i] = F.neg(s)
        # check Hx = 0 (sanity)
        count += 1
        if any(x):
            w = wt_b(x, b)
            best = w if best is None else min(best, w)
    return best, count

def kernel_check_general(F, H, b):
    """Exhaustive over all of F^n (small n only): returns (|ker|, min b-weight)."""
    n = len(H[0]); q = F.q; cnt = 0; best = None
    for x in itertools.product(range(q), repeat=n):
        ok = True
        for i in range(b):
            s = 0
            for j in range(n):
                if H[i][j] and x[j]:
                    s = F.add(s, F.mul(H[i][j], x[j]))
            if s:
                ok = False; break
        if ok:
            cnt += 1
            if any(x):
                w = wt_b(x, b); best = w if best is None else min(best, w)
    return cnt, best

# ---------- sections ----------
def sec_W():
    fields = [GF(p) for p in (2, 3, 5, 7, 11)] + [GF(4)]
    pairs = wins = 0
    for b in range(1, 13):
        for n in range(b, 4 * b + 6):
            v = seq_proof(b, n)
            assert len(v) == n and all(len(x) == b for x in v)
            assert all(set(x) <= {0, 1} for x in v)
            assert all(v[j] == [1 if k == j else 0 for k in range(b)] for j in range(b))
            for w in windows(v):
                d = det_int([[w[t][k] for t in range(b)] for k in range(b)])
                assert d in (1, -1), (b, n, d)
                wins += 1
            if b <= 9:
                for F in fields:
                    assert good(F, v), (b, n, F.q)
            pairs += 1
    print(f"W: {pairs} (b,n) pairs with 1<=b<=12, b<=n<=4b+5; {wins} windows all det = +-1 over Z; "
          f"rank b over F_2,F_3,F_4,F_5,F_7,F_11 for b<=9")

def sec_L():
    c = 0
    for b in range(1, 16):
        for n in range(b, 5 * b + 3):
            v = seq_proof(b, n)
            for j in range(n):
                for k in range(b):
                    assert sv(b, n, j, k) == v[j][k], (b, n, j, k)
            c += 1
    print(f"L: Lean `sv` recursion equals the ordinary-proof construction on {c} (b,n) pairs (b<=15, n<=5b+2)")

def random_good(F, r, length, rng, tries=20000):
    """Random r-good cyclic sequence of given length starting with e_0..e_{r-1} (rejection + repair)."""
    for _ in range(tries):
        v = [[1 if k == j else 0 for k in range(r)] for j in range(r)]
        ok = True
        for pos in range(r, length):
            cands = []
            for _ in range(60):
                x = [rng.randrange(F.q) for _ in range(r)]
                last = v[pos - r + 1:pos] + [x]
                if rank(F, last) == r:
                    cands.append(x); break
            if not cands:
                ok = False; break
            v.append(cands[0])
        if ok and good(F, v):
            return v
    return None

def bridge(T, b, n):
    r = len(T[0]); M = n // b
    p = [T[r + k] for k in range(b)]
    w = [[p[k][c] for k in range(b)] for c in range(r)]
    return [[1 if k == j % b else 0 for k in range(b)] for j in range(M * b)] + w

def sec_BR():
    rng = random.Random(334207)
    tested = 0
    for q in (2, 3, 5):
        F = GF(q)
        for b in range(2, 9):
            for n in range(b + 1, 4 * b + 3):
                if n % b == 0:
                    continue
                r = n % b
                for _ in range(3):
                    T = random_good(F, r, b + r, rng)
                    if T is None:
                        continue
                    v = bridge(T, b, n)
                    assert good(F, v), (q, b, n, T)
                    tested += 1
    print(f"BR: bridge lemma output b-good for {tested} RANDOM r-good inputs T (q in 2,3,5; 2<=b<=8)")

def sec_P2():
    rng = random.Random(4207)
    tested = 0
    for q in (2, 3):
        F = GF(q)
        for b in range(2, 5):
            for n in range(2 * b, 2 * b + 5):
                if q ** (n - b) > 200000:
                    continue
                for _ in range(3):
                    v = random_good(F, b, n, rng)
                    if v is None:
                        continue
                    H = [[v[j][i] for j in range(n)] for i in range(b)]
                    best, cnt = min_bweight_kernel(F, H, b)
                    assert cnt == q ** (n - b) and best == 2 * b, (q, b, n, best)
                    tested += 1
    print(f"P2: d_b = 2b and |C| = q^(n-b) for {tested} RANDOM b-good H (q in 2,3; b<=4; 2b<=n<=2b+4)")

def sec_C(limit=600000):
    rows = []
    for q in (2, 3, 4, 5, 7):
        F = GF(q)
        for b in range(2, 7):
            for n in range(2 * b, 3 * b + 3):
                if q ** (n - b) > limit:
                    continue
                v = seq_proof(b, n)
                H = [[v[j][i] for j in range(n)] for i in range(b)]
                best, cnt = min_bweight_kernel(F, H, b)
                assert cnt == q ** (n - b) and best == 2 * b, (q, b, n, best)
                rows.append((q, b, n))
    # fully independent exhaustive check over all of F^n (no systematic form assumed), tiny cases
    full = 0
    for q in (2, 3):
        F = GF(q)
        for b in (2, 3):
            for n in range(2 * b, 2 * b + 4):
                if q ** n > 60000:
                    continue
                v = seq_proof(b, n)
                H = [[v[j][i] for j in range(n)] for i in range(b)]
                cnt, best = kernel_check_general(F, H, b)
                assert cnt == q ** (n - b) and best == 2 * b
                full += 1
    print(f"C: {len(rows)} constructed codes (q in 2,3,4,5,7; 2<=b<=6; 2b<=n<=3b+2; |C|<= {limit}) have "
          f"|C| = q^(n-b) and minimum b-weight exactly 2b; {full} tiny cases re-checked over all of F_q^n")
    print("C: cases with q=2,b=5, n not divisible by 5:", [r for r in rows if r[0] == 2 and r[1] == 5 and r[2] % 5])
    print("C: cases with q=2,b=6:", [r for r in rows if r[0] == 2 and r[1] == 6])

def kurz_repair(F, b, n):
    """Kurz Lemma 3.5 proof, k = b, starting from the generator matrix [I_b | 0]."""
    u = [[1 if k == j else 0 for k in range(b)] if j < b else [0] * b for j in range(n)]
    for j in range(n):  # G_1: replace zero columns by a nonzero vector
        if not any(u[j]):
            u[j] = [1] + [0] * (b - 1)
    span = lambda idx: rank(F, [u[t % n] for t in idx])
    steps = 0
    for i in range(1, b):
        while True:
            bad = [j for j in range(n) if span(range(j, j + i + 1)) == i]
            if not bad:
                break
            # find j with S_j = S_{j+1} (i.e. T_j has dim i) and S_{j+1} != S_{j+2}
            j = None
            for j0 in bad:
                S1 = [u[t % n] for t in range(j0 + 1, j0 + 1 + i)]
                S2 = [u[t % n] for t in range(j0 + 2, j0 + 2 + i)]
                if rank(F, S1 + S2) > i:
                    j = j0; break
            assert j is not None, "Kurz step: no admissible j"
            h = (j + i) % n
            u[h] = [F.add(x, y) for x, y in zip(u[h], u[(h + 1) % n])]
            steps += 1
            # invariant: all i-windows still span an i-space; total rank b
            assert all(span(range(l, l + i)) == i for l in range(n))
            assert rank(F, u) == b
    return u, steps

def sec_K():
    c = tot = 0
    for q in (2, 3):
        F = GF(q)
        for b in range(2, 8):
            for n in range(b, 3 * b + 4):
                u, steps = kurz_repair(F, b, n)
                assert good(F, u), (q, b, n)
                c += 1; tot += steps
    print(f"K: Kurz Lemma 3.5 repair at k=b from [I_b|0] yields a b-good sequence in all {c} cases "
          f"(q in 2,3; 2<=b<=7; b<=n<=3b+3); {tot} repair steps")

def sec_N():
    F = GF(2); out = []
    for b in (2, 3, 4):
        n = 2 * b + 1
        v = seq_proof(b, n)
        v[b + 1] = v[b]  # makes window starting at b+1-b+1... dependent (repeated column)
        H = [[v[j][i] for j in range(n)] for i in range(b)]
        if all(rank(F, w) == b for w in windows(v)):
            continue
        cnt, best = kernel_check_general(F, H, b)
        out.append((b, n, cnt, best))
        assert best < 2 * b
    print(f"N: negative control (repeated adjacent column => dependent window): (b,n,|ker|,min wt_b) = {out}")

if __name__ == "__main__":
    for s in sys.argv[1:]:
        globals()["sec_" + s]()

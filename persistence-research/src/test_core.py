"""Validation gates for the persistence project. Run: python3 src/test_core.py

Every gate must pass before any large-scale search is trusted.
"""
import random
import sys
import time
from math import prod

sys.path.insert(0, sys.path[0])  # run as a script from src/
from persistence import (digit_product, persistence, persistence_naive, chain,
                         is_7smooth, smooth, prime_digit_expansion,
                         len23_table, len_of_smooth)

FAILURES = []


def check(name, cond, detail=""):
    status = "PASS" if cond else "FAIL"
    print(f"[{status}] {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILURES.append(name)


# ---------------------------------------------------------------------------
# 1. persistence() == persistence_naive() on a range + randoms
# ---------------------------------------------------------------------------
def test_shortcut_equivalence():
    bad = [n for n in range(0, 200_000) if persistence(n) != persistence_naive(n)]
    check("persistence == naive on [0, 2e5)", not bad, f"bad={bad[:5]}")
    rng = random.Random(20260214)
    bad = []
    for _ in range(3000):
        n = rng.randrange(1, 10 ** rng.randrange(2, 60))
        if persistence(n) != persistence_naive(n):
            bad.append(n)
    check("persistence == naive on 3000 random big ints", not bad, f"bad={bad[:5]}")


# ---------------------------------------------------------------------------
# 2. F5: brute force below 10^7 -> max persistence 8, first at 2677889
# ---------------------------------------------------------------------------
def test_brute_1e7():
    """DP: pi[n] = Pi(n) via pi[n] = pi[n//10] * (n%10); pers[n] = 1 + pers[pi[n]]
    (valid since pi[n] < n for n >= 10, F3). O(1) work per n."""
    from array import array
    t0 = time.time()
    N = 10 ** 7
    pi = array("q", bytes(8 * N))
    pers = array("b", bytes(N))
    for n in range(10):
        pi[n] = n
    for n in range(10, N):
        pi[n] = pi[n // 10] * (n % 10)
    best, argmin_best = 0, 0
    for n in range(10, N):
        p = 1 + pers[pi[n]]
        pers[n] = p
        if p > best:
            best, argmin_best = p, n
    # cross-check the DP persistence against the library on a sample
    rng = random.Random(7)
    sample_ok = all(persistence(n) == pers[n] for n in rng.sample(range(1, N), 5000))
    check("max P below 10^7 == 8 (OEIS A003001 s_8=2677889)",
          best == 8 and argmin_best == 2677889 and sample_ok,
          f"best={best} at {argmin_best}, {time.time()-t0:.1f}s")


# ---------------------------------------------------------------------------
# 3. len23 DP vs brute-force DFS
# ---------------------------------------------------------------------------
DIGIT_VECS = {2: (1, 0), 3: (0, 1), 4: (2, 0), 6: (1, 1), 8: (3, 0), 9: (0, 2)}


def len23_brute(a, b):
    """Independent check: DFS over digit choices with an admissible lower bound
    (each digit removes at most 3 from a and at most 2 from b)."""
    from math import ceil
    best = 10 ** 9

    def dfs(ra, rb, k):
        nonlocal best
        if ra == 0 and rb == 0:
            best = min(best, k)
            return
        if k + max(ceil(ra / 3), ceil(rb / 2)) >= best:
            return
        for d, (da, db) in DIGIT_VECS.items():
            if da <= ra and db <= rb:
                dfs(ra - da, rb - db, k + 1)

    dfs(a, b, 0)
    return best


def test_len23():
    t = len23_table(40, 40)
    ok = True
    bad = None
    for a in range(0, 13):
        for b in range(0, 13):
            if t[a][b] != len23_brute(a, b):
                ok, bad = False, (a, b, t[a][b], len23_brute(a, b))
    check("len23 DP == brute B&B for a,b < 13", ok, str(bad))


# ---------------------------------------------------------------------------
# 4. Domain completeness at D=5: brute max P below 10^5 == 1 + max_{𝓜_5} P
# ---------------------------------------------------------------------------
def max_domain_P(D):
    """Max P(m) over all m = 2^a 3^b 5^c 7^d with len23(a,b)+c+d <= D."""
    t23 = len23_table(3 * D + 3, 2 * D + 3)
    best, arg = -1, None
    for a in range(3 * D + 3):
        for b in range(2 * D + 3):
            l23 = t23[a][b]
            if l23 > D:
                continue
            mab = 2 ** a * 3 ** b
            rem = D - l23
            for c in range(rem + 1):
                mc = mab * 5 ** c
                for d in range(rem - c + 1):
                    m = mc * 7 ** d
                    p = persistence(m)
                    if p > best:
                        best, arg = p, (a, b, c, d, m)
    return best, arg


def test_domain_D5():
    # brute force side
    best, argmin_best = 0, 0
    for n in range(10, 10 ** 5):
        p = persistence(n)
        if p > best:
            best, argmin_best = p, n
    check("max P below 10^5 == 7 (s_7 = 68889)", best == 7 and argmin_best == 68889,
          f"best={best} at {argmin_best}")
    md, arg = max_domain_P(5)
    check("1 + max_{𝓜_5} P == 7 (domain completeness ↔ brute force)",
          1 + md == 7, f"maxdomain P = {md} at (a,b,c,d,m)={arg}")


# ---------------------------------------------------------------------------
# 5. Known values
# ---------------------------------------------------------------------------
def test_known():
    rec = 277777788888899
    c = chain(rec)
    check("P(277777788888899) == 11 (naive)", persistence_naive(rec) == 11)
    check("P(277777788888899) == 11 (fast)", persistence(rec) == 11)
    check("record chain matches literature",
          c == [277777788888899, 4996238671872, 438939648, 4478976, 338688,
                27648, 2688, 768, 336, 54, 20, 0], str(c))
    check("P(4996238671872) == 10", persistence(4996238671872) == 10)
    check("P(2677889) == 8", persistence(2677889) == 8)
    check("4996238671872 is 7-smooth", is_7smooth(4996238671872))
    check("277777788888899 is NOT 7-smooth", not is_7smooth(rec))
    check("Pi(prime_digit_expansion(a,b,c,d)) == smooth(a,b,c,d)",
          all(digit_product(prime_digit_expansion(a, b, c, d)) == smooth(a, b, c, d)
              for a, b, c, d in [(1, 0, 0, 0), (0, 2, 1, 3), (19, 4, 0, 6), (0, 0, 0, 0)]))


def main():
    t0 = time.time()
    test_shortcut_equivalence()
    test_len23()
    test_known()
    test_domain_D5()
    test_brute_1e7()
    print(f"\n{'ALL GATES PASSED' if not FAILURES else 'FAILURES: ' + str(FAILURES)}"
          f"  [{time.time()-t0:.1f}s]")
    sys.exit(1 if FAILURES else 0)


if __name__ == "__main__":
    main()

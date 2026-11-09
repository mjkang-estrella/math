"""
Fonga's V-function (arXiv:2608.27802, Thm 4.1, eqs (14)-(15)) for base 10, p = 2.

V(D) = max{ v_2(9n) : n has digit multiset {1s} + D }  (D = exceptional digits)

Equation: 9n = 10^L + sum_{d in D} 9(d-1) 10^{r_d} - 1,  r_1 < r_2 < ... < L-1.
Recursion (14): V(M, a, T) = max( v2(T),
                                  max_{d in M, a < t <= v2(T)} V(M-{d}, t, T + 9(d-1) 10^t) )
Terminal  (15): V({}, a, T) = max( v2(T), max_{a < L <= v2(T)} v2(T + 10^L) )
Initialization: V(D) = max_{d in D} V(D-{d}, 0, 9(d-1) - 1);  V({}) = 0  (10^L - 1 is odd).
"""
import sys
from functools import lru_cache
sys.set_int_max_str_digits(100000)

def v2(x: int) -> int:
    if x == 0:
        return 10**9
    return (x & -x).bit_length() - 1

def Vunga(D, verbose=False):
    """Max v_2(9n) over the family with exceptional digit multiset D (tuple)."""
    D = tuple(sorted(D))
    if not D:
        return 0  # 9n = 10^L - 1, odd
    best = 0
    memo = {}
    def rec(M, a, T):
        # M: remaining multiset (sorted tuple), a: last placed position, T: partial sum
        nonlocal best
        vt = v2(T)
        if vt > best: best = vt
        if not M:
            # terminal: L in (a, vt]
            for L in range(a + 1, min(vt, 5000) + 1):
                w = v2(T + (1 << 0) * 0 + 10**L) if L < 4000 else None
                if w is None:
                    w = v2(T + 10**L)
                if w > best: best = w
            return
        key = (M, a, T)
        # memoization is unsound for 'best' side-effects; compute value bottom-up instead
        raise RuntimeError("use iterative version")
    # iterative DFS with explicit value computation
    from functools import lru_cache
    @lru_cache(maxsize=None)
    def val(M, a, T):
        vt = v2(T)
        r = vt
        if not M:
            for L in range(a + 1, min(vt, 3000) + 1):
                w = v2(T + 10**L)
                if w > r: r = w
            return r
        seen = set()
        for i, d in enumerate(M):
            if d in seen: continue
            seen.add(d)
            M2 = M[:i] + M[i+1:]
            for t in range(a + 1, vt + 1):
                v = val(M2, t, T + 9 * (d - 1) * 10**t)
                if v > r: r = v
        return r
    seen0 = set()
    for i, d in enumerate(D):
        if d in seen0: continue
        seen0.add(d)
        v = val(D[:i] + D[i+1:], 0, 9 * (d - 1) - 1)
        if v > best: best = v
    return best

def brute_V(D, Lmax=14):
    """Brute force max v_2(9n) over all n with digits {1s}+D and total length <= Lmax."""
    from itertools import permutations
    D = tuple(sorted(D))
    best = 0
    L0 = len(D)
    for L in range(max(L0, 1), Lmax + 1):
        # positions for the exceptional digits: choose L0 positions out of L, assign digits
        import itertools
        for pos in itertools.combinations(range(L), L0):
            for assign in set(itertools.permutations(D)):
                n = (10**L - 1) // 9
                for p, d in zip(pos, assign):
                    n += (d - 1) * 10**p
                w = v2(9 * n)
                if w > best: best = w
    return best

if __name__ == "__main__":
    import itertools, time
    print("=== Vunga (Fonga V) validation vs brute force ===")
    fams = [(2,), (3,), (4,), (5,), (6,), (7,), (8,), (9,),
            (2,2), (2,3), (4,4), (7,7), (2,4,7), (3,3,3), (5,5,5), (8,8,8),
            (2,2,2), (6,6,6), (9,9,9), (4,4,7), (2,4), (3,7), (5,2)]
    ok = True
    for D in fams:
        t0 = time.time()
        v1 = Vunga(D)
        v2b = brute_V(D, Lmax=13)
        stat = "OK " if v1 == v2b else "MISMATCH"
        if v1 != v2b: ok = False
        print(f"D={D}: Vunga={v1}  brute={v2b}  [{stat}]  ({time.time()-t0:.1f}s)")
    print("ALL OK" if ok else "*** FAILURES ***")

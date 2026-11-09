"""Brute force: P_n = sum_y |s^-1(y)|^2 for West's stack-sorting map, written from the
source definition s(L m R) = s(L) s(R) m (Defant-Propp Section 2.3).  Also records the
maximum fibre size (compared with the Catalan number) and checks the elementary
2^(n-1) family of preimages of the identity.  Written independently of the r133 lane."""
import sys, itertools, json
from collections import Counter
from math import comb


def s_rec(w):
    """Literal recursive definition."""
    if not w:
        return ()
    m = max(w)
    k = w.index(m)
    return s_rec(w[:k]) + s_rec(w[k + 1:]) + (m,)


def s_stack(w):
    """Knuth/West one-pass stack: push, popping smaller tops first."""
    out, st = [], []
    for x in w:
        while st and st[-1] < x:
            out.append(st.pop())
        st.append(x)
    while st:
        out.append(st.pop())
    return tuple(out)


def family(n):
    """pi in F_n iff pi = n pi' or pi = pi' n with pi' in F_{n-1}."""
    F = {()}
    for k in range(1, n + 1):
        F = {(k,) + p for p in F} | {p + (k,) for p in F}
    return F


nmax_rec = int(sys.argv[1]) if len(sys.argv) > 1 else 8
nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 10
res = {}
for n in range(1, nmax + 1):
    cnt = Counter()
    for p in itertools.permutations(range(1, n + 1)):
        y = s_stack(p)
        if n <= nmax_rec:
            assert y == s_rec(p), (p, y)
        cnt[y] += 1
    P = sum(v * v for v in cnt.values())
    mx = max(cnt.values())
    ident = tuple(range(1, n + 1))
    cat = comb(2 * n, n) // (n + 1)
    fam = family(n) if n <= 12 else set()
    fam_ok = all(s_rec(p) == ident for p in fam) and len(fam) == 2 ** (n - 1)
    res[n] = {"P": P, "max_fibre": mx, "fibre_of_id": cnt[ident], "catalan": cat,
              "family_2^(n-1)_ok": fam_ok}
    print(n, P, "max", mx, "id", cnt[ident], "C_n", cat, "fam", fam_ok, flush=True)
json.dump(res, open("outputs/brute_P.json", "w"), indent=1)

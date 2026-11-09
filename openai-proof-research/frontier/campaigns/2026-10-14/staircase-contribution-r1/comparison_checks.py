"""Finite sanity checks for two comparison arguments in review.md.

Original code (c) 2026 Myeongjin Kang, MIT licence. Written independently in
this review directory; imports no candidate or proof-review program.

C1 (integral restriction lemma): for h in the row group H_R, the coefficient of
    the antidiagonal word beta in h.v_C is +-1 if h=1 and 0 otherwise.
C2 (single-monomial reformulation): a position permutation g fixing beta
    (g in the antidiagonal group H_A) for which col o g has every row palette
    {1..r} is the identity.  Checked by exhaustion over H_A.
C3 hook lengths of the staircase are the odd numbers 1,3,...,2m-1, so rho_m is a
    p-core exactly for p=2 or p>2m-1.
Finite checks only; the all-m statements are proved in review.md.
"""
import itertools, math, sys

def cells(m):
    return [(i, j) for i in range(1, m + 1) for j in range(1, m + 2 - i)]

def beta(m, c):
    return m + 2 - c[0] - c[1]

def perm_sign(p):
    s, seen = 1, set()
    for k in range(len(p)):
        if k in seen:
            continue
        L, x = 0, k
        while x not in seen:
            seen.add(x); x = p[x]; L += 1
        s *= (-1) ** (L - 1)
    return s

def coeff_in_vC(m, word):
    """Coefficient of a word (dict cell->letter) in v_C = tensor_j alt(C_j)."""
    total = 1
    for j in range(1, m + 1):
        col = [word[(i, j)] for i in range(1, m + 2 - j)]
        if sorted(col) != list(range(1, len(col) + 1)):
            return 0
        total *= perm_sign([x - 1 for x in col])
    return total

def check_C1(m):
    B = cells(m)
    rows = [[(i, j) for j in range(1, m + 2 - i)] for i in range(1, m + 1)]
    b = {c: beta(m, c) for c in B}
    count = 0
    for perms in itertools.product(*[itertools.permutations(r) for r in rows]):
        g = {}
        for r, p in zip(rows, perms):
            g.update(dict(zip(r, p)))
        # coefficient of beta in h.v_C equals coefficient of beta o h in v_C
        w = {c: b[g[c]] for c in B}
        cf = coeff_in_vC(m, w)
        ident = all(g[c] == c for c in B)
        assert (cf != 0) == ident, (m, g, cf)
        if ident:
            assert abs(cf) == 1
        count += 1
    return count

def check_C2(m):
    B = cells(m)
    anti = {}
    for c in B:
        anti.setdefault(c[0] + c[1], []).append(c)
    blocks = list(anti.values())
    count = 0
    for perms in itertools.product(*[itertools.permutations(bl) for bl in blocks]):
        g = {}
        for bl, p in zip(blocks, perms):
            g.update(dict(zip(bl, p)))
        ok = all(sorted(g[(i, j)][1] for j in range(1, m + 2 - i)) ==
                 list(range(1, m + 2 - i)) for i in range(1, m + 1))
        ident = all(g[c] == c for c in B)
        assert ok == ident, (m, g)
        count += 1
    return count

def check_C3(m):
    lam = list(range(m, 0, -1))
    conj = [sum(1 for x in lam if x >= k) for k in range(1, m + 1)]
    hooks = sorted(lam[i] - j + conj[j - 1] - (i + 1) + 1
                   for i in range(m) for j in range(1, lam[i] + 1))
    assert sorted(set(hooks)) == list(range(1, 2 * m, 2)), hooks
    return len(hooks)

if __name__ == "__main__":
    out = []
    for m in range(1, 5):
        out.append(f"C1 m={m}: {check_C1(m)} row-group elements checked")
    for m in range(1, 6):
        out.append(f"C2 m={m}: {check_C2(m)} antidiagonal-group elements checked")
    for m in range(1, 13):
        check_C3(m)
    out.append("C3 m=1..12: staircase hook lengths are exactly the odd numbers <= 2m-1")
    print("\n".join(out))
    print("ALL PASS")

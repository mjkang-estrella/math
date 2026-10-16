#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see ../fresh-algebra-discovery-r1/LICENSE-CODE).
"""Finite controls for the contribution review of the staircase cube candidate.

Written independently of the candidate's and proof reviewer's programs.

(A) Product-coordinate form.  For the staircase triangle B, let
    beta(i,j) = m+2-i-j and b0(i,j) = j.  The coefficient of the basis
    triple e_beta (x) e_b0 (x) e_beta in g.z, with z = v_R (x) v_R (x) v_C, is
    cR(beta o g) * cR(b0 o g) * cC(beta o g).  We enumerate, by complete
    backtracking over positions (pruning only by the literal per-block
    alternation support rule), every g in Sym(B) for which this product is
    nonzero, for m = 1..5.  Expected: only g = identity, product +1.

(B) Integral obstruction to the I21 route at m = 2, p = 2: the trivial module
    is a direct summand of M^(2,1) over F_2 (index 3 is odd), but not of
    S^(2,1) (x) S^(2,1) over F_2.  Hence M^rho is not a summand of the
    Specht square there, so the complex identification of I21 cannot be a
    split integral statement in general.
"""
import itertools
import json
import sys


def triangle(m):
    return [(i, j) for i in range(1, m + 1) for j in range(1, m + 2 - i)]


def perm_sign(seq):
    seq = list(seq)
    sign = 1
    seen = [False] * len(seq)
    for s in range(len(seq)):
        if seen[s]:
            continue
        length = 0
        t = s
        while not seen[t]:
            seen[t] = True
            t = seq[t] - 1
            length += 1
        if length % 2 == 0:
            sign = -sign
    return sign


def coeff(word, blocks):
    """Coefficient of e_word in the ordered alternating block tensor."""
    c = 1
    for blk in blocks:
        vals = [word[x] for x in blk]
        if sorted(vals) != list(range(1, len(blk) + 1)):
            return 0
        c *= perm_sign(vals)
    return c


def part_a(m):
    B = triangle(m)
    rows = [[(i, j) for j in range(1, m + 2 - i)] for i in range(1, m + 1)]
    cols = [[(i, j) for i in range(1, m + 2 - j)] for j in range(1, m + 1)]
    beta = {(i, j): m + 2 - i - j for (i, j) in B}
    b0 = {(i, j): j for (i, j) in B}
    row_of = {x: k for k, r in enumerate(rows) for x in r}
    col_of = {x: k for k, c in enumerate(cols) for x in c}
    # g is built as an assignment x -> g(x); the three pulled-back words are
    # beta o g (row and column support) and b0 o g (row support).
    found = []
    used_rb = [set() for _ in rows]
    used_cb = [set() for _ in cols]
    used_r0 = [set() for _ in rows]
    image = {}
    taken = set()

    def rec(k):
        if k == len(B):
            found.append(dict(image))
            return
        x = B[k]
        ri, ci = row_of[x], col_of[x]
        rlen, clen = len(rows[ri]), len(cols[ci])
        for y in B:
            if y in taken:
                continue
            vb, v0 = beta[y], b0[y]
            if vb > rlen or vb in used_rb[ri]:
                continue
            if vb > clen or vb in used_cb[ci]:
                continue
            if v0 > rlen or v0 in used_r0[ri]:
                continue
            taken.add(y)
            image[x] = y
            used_rb[ri].add(vb)
            used_cb[ci].add(vb)
            used_r0[ri].add(v0)
            rec(k + 1)
            used_rb[ri].discard(vb)
            used_cb[ci].discard(vb)
            used_r0[ri].discard(v0)
            del image[x]
            taken.discard(y)

    rec(0)
    results = []
    for g in found:
        wb = {x: beta[g[x]] for x in B}
        w0 = {x: b0[g[x]] for x in B}
        prod = coeff(wb, rows) * coeff(w0, rows) * coeff(wb, cols)
        results.append({"identity": all(g[x] == x for x in B), "product": prod})
    return {"m": m, "N": len(B), "nonzero_translates": len(results), "results": results}


# ---------- linear algebra over F_p ----------

def rank_mod(rows, p):
    rows = [list(r) for r in rows]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for c in range(ncols):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c] % p:
                f = rows[r][c]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[rank])]
        rank += 1
    return rank


def nullspace_mod(mat, p):
    """Basis of {x : mat x = 0} over F_p; mat is a list of rows."""
    if not mat:
        return []
    n = len(mat[0])
    rows = [list(r) for r in mat]
    pivcols = []
    rank = 0
    for c in range(n):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c] % p:
                f = rows[r][c]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[rank])]
        pivcols.append(c)
        rank += 1
    free = [c for c in range(n) if c not in pivcols]
    basis = []
    for fcol in free:
        v = [0] * n
        v[fcol] = 1
        for r, pc in enumerate(pivcols):
            v[pc] = (-rows[r][fcol]) % p
        basis.append(v)
    return basis


def trivial_is_summand(gens, dim, p):
    """gens: list of dim x dim integer matrices (action on column vectors)."""
    eqs = []
    for A in gens:
        for r in range(dim):
            eqs.append([(A[r][c] - (1 if r == c else 0)) % p for c in range(dim)])
    inv = nullspace_mod(eqs, p)
    eqs_d = []
    for A in gens:
        for c in range(dim):
            eqs_d.append([(A[r][c] - (1 if r == c else 0)) % p for r in range(dim)])
    coinv = nullspace_mod(eqs_d, p)
    pair = [[sum(a * b for a, b in zip(phi, v)) % p for v in inv] for phi in coinv]
    nonzero = any(x for row in pair for x in row)
    return {"invariants": len(inv), "coinvariant_functionals": len(coinv),
            "trivial_summand": bool(nonzero)}


def part_b():
    p = 2
    m = 2
    B = triangle(m)
    rows = [[(1, 1), (1, 2)], [(2, 1)]]
    cols = [[(1, 1), (2, 1)], [(1, 2)]]
    # S^(2,1) as span of column polytabloids in content-(2,1) words.
    words = [w for w in itertools.product([1, 2], repeat=3) if sorted(w) == [1, 1, 2]]
    widx = {w: k for k, w in enumerate(words)}

    def act(g, w):
        # (g e_a)(x) = a(g^{-1} x); positions indexed 0..2 in B order
        ginv = [0] * 3
        for s in range(3):
            ginv[g[s]] = s
        return tuple(w[ginv[s]] for s in range(3))

    # polytabloid for tableau with columns ((1,1),(2,1)) and ((1,2)) in B-index terms
    pos = {x: k for k, x in enumerate(B)}
    base = [0] * len(words)
    for a in (1, 2):
        w = [0, 0, 0]
        w[pos[(1, 1)]] = a
        w[pos[(2, 1)]] = 3 - a
        w[pos[(1, 2)]] = 1
        base[widx[tuple(w)]] += 1 if a == 1 else -1
    G = list(itertools.permutations(range(3)))
    span = []
    for g in G:
        v = [0] * len(words)
        for w, c in zip(words, base):
            if c:
                v[widx[act(g, w)]] += c
        span.append(v)
    # integer basis of S: two independent orbit vectors (rank 2 over Q and F_2)
    basis = []
    for v in span:
        if rank_mod(basis + [v], 2) > len(basis) and rank_mod(basis + [v], 3) > len(basis):
            basis.append(v)
    assert len(basis) == 2

    def coords(v):
        # solve v = x0*b0 + x1*b1 over Z (unimodular check via both primes)
        for x0 in range(-3, 4):
            for x1 in range(-3, 4):
                if all(x0 * a + x1 * b == c for a, b, c in zip(basis[0], basis[1], v)):
                    return [x0, x1]
        raise AssertionError("not in lattice span")

    gens = [(1, 0, 2), (0, 2, 1)]  # position transpositions generating S_3
    mats_S = []
    for g in gens:
        cols_ = []
        for b in basis:
            v = [0] * len(words)
            for w, c in zip(words, b):
                if c:
                    v[widx[act(g, w)]] += c
            cols_.append(coords(v))
        mats_S.append([[cols_[c][r] for c in range(2)] for r in range(2)])
    mats_SS = [[[A[r1][c1] * A[r2][c2] for c1 in range(2) for c2 in range(2)]
                for r1 in range(2) for r2 in range(2)] for A in mats_S]
    mats_M = []
    for g in gens:
        A = [[0] * 3 for _ in range(3)]
        for c, w in enumerate(words):
            A[widx[act(g, w)]][c] = 1
        mats_M.append(A)
    return {
        "m": 2, "p": p,
        "S_tensor_S": trivial_is_summand(mats_SS, 4, p),
        "M_rho": trivial_is_summand(mats_M, 3, p),
        "pair_letter_scalar_mod_p": (2 * 1) % p,
    }


def brute_force(m, use_col=True, second="b0"):
    """Plain enumeration of Sym(B), no pruning; returns nonzero products."""
    B = triangle(m)
    rows = [[(i, j) for j in range(1, m + 2 - i)] for i in range(1, m + 1)]
    cols = [[(i, j) for i in range(1, m + 2 - j)] for j in range(1, m + 1)]
    beta = {(i, j): m + 2 - i - j for (i, j) in B}
    sec = {(i, j): (j if second == "b0" else m + 2 - i - j) for (i, j) in B}
    hits = []
    for img in itertools.permutations(B):
        g = dict(zip(B, img))
        wb = {x: beta[g[x]] for x in B}
        w2 = {x: sec[g[x]] for x in B}
        c = coeff(wb, rows) * coeff(w2, rows)
        if use_col:
            c *= coeff(wb, cols)
        if c:
            hits.append(c)
    return hits


def main():
    out = {"part_a": [], "part_b": None, "brute_force_m3": None}
    bf = brute_force(3)
    assert bf == [1], bf
    no_col = brute_force(3, use_col=False)
    triple_beta = brute_force(3, second="beta")
    out["brute_force_m3"] = {
        "permutations": 720,
        "candidate_coordinate_nonzero": len(bf),
        "mutation_drop_column_factor_nonzero": len(no_col),
        "mutation_second_coordinate_beta_nonzero": len(triple_beta),
    }
    assert len(no_col) > 1 and len(triple_beta) != 1
    for m in range(1, 6):
        r = part_a(m)
        assert r["nonzero_translates"] == 1, r
        assert r["results"][0]["identity"] and r["results"][0]["product"] == 1, r
        out["part_a"].append({k: r[k] for k in ("m", "N", "nonzero_translates")} |
                             {"only_identity_with_product_plus_one": True})
    b = part_b()
    assert b["M_rho"]["trivial_summand"] is True
    assert b["S_tensor_S"]["trivial_summand"] is False
    out["part_b"] = b
    json.dump(out, sys.stdout, indent=1, sort_keys=True)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()

"""Independent ordinary check of the MathDB 324342 counterexample.

Reads W only from the Lean source text (Wrows block); does not import any r3/r4 script or
certificate.  Checks: conference property, rank mod 19, membership of the Lean weight-9 word,
exact minimum distance via 12-column-subset ranks (method differs from r4's 10-set kernels),
and the Paley p=19 control.  Usage: python3 -I indep_check.py <lean file> <out json>
"""
import itertools, json, re, sys

P = 19


def parse_W(path):
    txt = open(path).read()
    blk = txt.split("def Wrows : List (List ℤ) := [", 1)[1].split("]]", 1)[0] + "]"
    rows = [[int(x) for x in r.split(",")] for r in re.findall(r"\[([^\[\]]+)\]", blk)]
    assert len(rows) == 20 and all(len(r) == 20 for r in rows)
    return rows


def rank_mod(M, p):
    M = [[x % p for x in r] for r in M]
    rk, cols = 0, len(M[0]) if M else 0
    for c in range(cols):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None:
            continue
        M[rk], M[piv] = M[piv], M[rk]
        inv = pow(M[rk][c], p - 2, p)
        M[rk] = [x * inv % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rk])]
        rk += 1
    return rk, M[:rk]


def min_distance(G, n, p):
    """d = smallest w such that some (n-w)-set of columns has rank < k."""
    k = len(G)
    cols = [[G[i][j] for i in range(k)] for j in range(n)]
    counts = {}
    for w in range(1, n - k + 2):
        bad = 0
        for S in itertools.combinations(range(n), n - w):
            if rank_mod([list(r) for r in zip(*[cols[j] for j in S])], p)[0] < k:
                bad += 1
        counts[w] = bad
        if bad:
            return w, counts
    return n - k + 1, counts


def main():
    lean, out = sys.argv[1], sys.argv[2]
    W = parse_W(lean)
    n = 20
    res = {}
    res["entries_ok"] = all(x in (0, 1, -1) for r in W for x in r)
    res["row_nnz"] = sorted({sum(1 for x in r if x) for r in W})
    res["col_nnz"] = sorted({sum(1 for r in W if r[j]) for j in range(n)})
    gram = [[sum(W[i][t] * W[j][t] for t in range(n)) for j in range(n)] for i in range(n)]
    res["gram_19I"] = all(gram[i][j] == (19 if i == j else 0) for i in range(n) for j in range(n))
    res["skew"] = all(W[i][j] == -W[j][i] for i in range(n) for j in range(n))
    res["zero_diag"] = all(W[i][i] == 0 for i in range(n))
    rk, G = rank_mod(W, P)
    res["rank_mod19"] = rk
    word = [0, 0, 0, 0, 0, 15, 0, 0, 10, 1, 18, 0, 9, 0, 18, 14, 5, 15, 0, 0]
    res["word_weight"] = sum(1 for x in word if x)
    res["word_in_code"] = rank_mod(G + [word], P)[0] == rk
    res["self_orthogonal_mod19"] = all(g % P == 0 for r in gram for g in r)
    d, counts = min_distance(G, n, P)
    res["min_distance_exact"] = d
    res["rank_deficient_colsets_by_w"] = counts
    # Paley control: bordered Paley conference matrix of order 20 (p = 19)
    chi = lambda a: 0 if a % P == 0 else (1 if pow(a % P, (P - 1) // 2, P) == 1 else -1)
    Q = [[0] + [1] * P] + [[-1] + [chi(j - i) for j in range(P)] for i in range(P)]
    gq = [[sum(Q[i][t] * Q[j][t] for t in range(n)) for j in range(n)] for i in range(n)]
    res["paley_conference"] = all(gq[i][j] == (19 if i == j else 0) for i in range(n) for j in range(n))
    rq, GQ = rank_mod(Q, P)
    res["paley_rank"] = rq
    dq, cq = min_distance(GQ, n, P)
    res["paley_min_distance"] = dq
    json.dump(res, open(out, "w"), indent=1)
    print(json.dumps(res))


if __name__ == "__main__":
    main()

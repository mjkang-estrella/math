"""Routineness probe: build the textbook Goethals-Seidel skew-Hadamard matrix of order 20 from
length-5 sequences (own implementation), set W = H - I, and compute the F_19 row-code minimum
distance with the subset-rank method of indep_check.py.  Also enumerate ALL +-1 quadruples
(a skew-type, b, c, d) of length 5 with zero total periodic autocorrelation (2^2 * 2^15 cases,
bounded) and record minimum distances for the first LIMIT distinct matrices only.
Usage: python3 -I gs_routine_check.py <out json>
"""
import itertools, json, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indep_check import rank_mod, min_distance  # noqa: E402

P, m = 19, 5
LIMIT = 6  # bounded: exact distance only for the first LIMIT distinct GS matrices


def circ(v):
    return [[v[(j - i) % m] for j in range(m)] for i in range(m)]


def mul(X, Y):
    return [[sum(X[i][t] * Y[t][j] for t in range(len(Y))) for j in range(len(Y[0]))] for i in range(len(X))]


def T(X):
    return [list(r) for r in zip(*X)]


def neg(X):
    return [[-x for x in r] for r in X]


R = [[1 if i + j == m - 1 else 0 for j in range(m)] for i in range(m)]


def gs(a, b, c, d):
    A, B, C, D = circ(a), circ(b), circ(c), circ(d)
    BR, CR, DR = mul(B, R), mul(C, R), mul(D, R)
    DtR, CtR, BtR = mul(T(D), R), mul(T(C), R), mul(T(B), R)
    blocks = [[A, BR, CR, DR],
              [neg(BR), A, DtR, neg(CtR)],
              [neg(CR), neg(DtR), A, BtR],
              [neg(DR), CtR, neg(BtR), A]]
    return [sum((blocks[I][J][i] for J in range(4)), []) for I in range(4) for i in range(m)]


def paf(v, s):
    return sum(v[i] * v[(i + s) % m] for i in range(m))


def code_d(H):
    n = len(H)
    W = [[H[i][j] - (1 if i == j else 0) for j in range(n)] for i in range(n)]
    ok = all(sum(W[i][t] * W[j][t] for t in range(n)) == (19 if i == j else 0)
             for i in range(n) for j in range(n)) and all(W[i][j] == -W[j][i] for i in range(n) for j in range(n))
    rk, G = rank_mod(W, P)
    return ok, rk, min_distance(G, n, P)[0]


def main():
    out = {}
    a, b, c, d = (1, 1, 1, -1, -1), (1, 1, 1, 1, -1), (1, 1, 1, 1, -1), (1, 1, -1, 1, -1)
    out["r4_sequences"] = dict(zip(["ok", "rank", "d"], code_d(gs(a, b, c, d))))
    pm = list(itertools.product((1, -1), repeat=m))
    skew_a = [v for v in pm if v[0] == 1 and all(v[m - i] == -v[i] for i in range(1, m))]
    quads, dist = 0, {}
    seen = set()
    for a in skew_a:
        for b in pm:
            for c in pm:
                for d in pm:
                    if all(paf(a, s) + paf(b, s) + paf(c, s) + paf(d, s) == 0 for s in range(1, m)):
                        quads += 1
                        H = gs(a, b, c, d)
                        key = tuple(map(tuple, H))
                        if key in seen:
                            continue
                        seen.add(key)
                        if len(seen) <= LIMIT:
                            ok, rk, dd = code_d(H)
                            assert ok and rk == 10
                            dist[dd] = dist.get(dd, 0) + 1
    out["gs_quadruples"] = quads
    out["distinct_matrices"] = len(seen)
    out["min_distance_histogram"] = dist
    json.dump(out, open(sys.argv[1], "w"), indent=1)
    print(json.dumps(out))


if __name__ == "__main__":
    main()

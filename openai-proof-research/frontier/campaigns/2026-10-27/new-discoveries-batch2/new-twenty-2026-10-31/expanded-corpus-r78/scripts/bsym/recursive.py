# Recursive construction, all entries 0/1 integers; claim: every cyclic b-window has determinant +-1 over Z,
# hence is a basis over EVERY field.
#   S(b, n) for n >= b:  b | n -> (e_0..e_{b-1})^(n/b)
#   else n = M b + r (M >= 1, 1 <= r < b): T = S(r, b + r) (starts with e_0..e_{r-1});
#        p_k = T[r + k] (k = 0..b-1) in Z^r; bridge vectors w_c = (p_0[c], ..., p_{b-1}[c]) in Z^b (c = 0..r-1);
#        S(b, n) = (e_0..e_{b-1})^M ++ (w_0, ..., w_{r-1}).
import sys, json
from fractions import Fraction
from functools import lru_cache
@lru_cache(maxsize=None)
def S(b, n):
    assert n >= b >= 1
    E = tuple(tuple(int(k == i) for k in range(b)) for i in range(b))
    if n % b == 0: return E * (n // b)
    M, r = divmod(n, b)
    T = S(r, b + r)
    assert T[:r] == tuple(tuple(int(k == i) for k in range(r)) for i in range(r))
    P = T[r:r + b]
    W = tuple(tuple(P[k][c] for k in range(b)) for c in range(r))
    return E * M + W
def det(rows):
    A = [[Fraction(x) for x in r] for r in rows]; n = len(A); d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None: return 0
        if p != c: A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            if A[i][c]:
                f = A[i][c] / A[c][c]; A[i] = [x - f*y for x, y in zip(A[i], A[c])]
    return d
if __name__ == '__main__':
    B, extra = int(sys.argv[1]), int(sys.argv[2])
    bad = []; cnt = 0; windows = 0
    for b in range(1, B + 1):
        for n in range(b, 3 * b + extra):
            seq = S(b, n); cnt += 1
            assert len(seq) == n and all(x in (0, 1) for v in seq for x in v)
            for s in range(n):
                windows += 1
                d = det([seq[(s + j) % n] for j in range(b)])
                if abs(d) != 1: bad.append((b, n, s, str(d))); break
    print(json.dumps({'B': B, 'n_range': 'b..3b+%d' % (extra - 1), 'pairs': cnt, 'windows_checked': windows, 'bad': bad[:10], 'nbad': len(bad)}))
    for b, n in [(5, 11), (5, 12), (5, 13), (5, 14), (7, 17)]:
        print(b, n, [''.join(map(str, v)) for v in S(b, n)])

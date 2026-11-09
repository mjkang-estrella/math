# Exact Voronoi-game equilibrium checker on Q_n (pure Python, integer arithmetic).
# Definitions follow Stylianou arXiv:2510.25392 Section 1: voters at every vertex, vote split
# equally among the players at minimum Hamming distance; a profile is an equilibrium when no
# single player can strictly increase its score by moving to another vertex.
# Method: for player i, with the other players fixed, voter x has minimum distance m(x) to the
# others and c(x) ties. A deviator at distance t from x gets L if t<m, L/(c+1) if t=m, else 0
# (L = lcm(1..k)). This equals A_x [t<=m-1] + B_x [t<=m] with B=L/(c+1), A=L-B, so the score
# at every position q is a sum of XOR-convolutions with Hamming balls, computed by one
# Walsh-Hadamard transform per radius.  Exact integers throughout.
from math import lcm, comb

def wht(a):
    a = list(a); n = len(a); h = 1
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                x = a[j]; y = a[j + h]
                a[j] = x + y; a[j + h] = x - y
        h *= 2
    return a

_ball_cache = {}
def ball_hats(n):
    if n in _ball_cache: return _ball_cache[n]
    V = 1 << n
    # Krawtchouk K_j(w) = sum_i (-1)^i C(w,i) C(n-w,j-i)
    K = [[sum((-1) ** i * comb(w, i) * comb(n - w, j - i) for i in range(0, j + 1)) for w in range(n + 1)] for j in range(n + 1)]
    cum = []
    for r in range(n + 1):
        cum.append([sum(K[j][w] for j in range(r + 1)) for w in range(n + 1)])
    pc = [bin(x).count('1') for x in range(V)]
    hats = [[cum[r][pc[x]] for x in range(V)] for r in range(n + 1)]
    _ball_cache[n] = (hats, pc)
    return _ball_cache[n]

def scores(n, pos, i, L=None):
    """Return list S with S[q] = L*2^n*(score of player i if it moves to q) * ... scaled:
    S[q] = sum_x share_x(q) * L  (an integer); true score = S[q] / (L * 2^n)."""
    k = len(pos); V = 1 << n
    if L is None: L = lcm(*range(1, k + 1))
    hats, pc = ball_hats(n)
    others = [pos[j] for j in range(k) if j != i]
    U = [[0] * V for _ in range(n + 1)]
    for x in range(V):
        ds = [pc[x ^ p] for p in others]
        m = min(ds); c = ds.count(m)
        B = L // (c + 1); A = L - B
        U[m][x] += B
        if m >= 1: U[m - 1][x] += A
    tot = [0] * V
    for r in range(n + 1):
        if any(U[r]):
            Ur = wht(U[r]); h = hats[r]
            for w in range(V): tot[w] += Ur[w] * h[w]
    S = wht(tot)
    return [s // V for s in S]  # exact: inverse WHT divides by V

def is_equilibrium(n, pos, early=True):
    """Returns (bool, details). details: list of (i, current, best, argbest)."""
    k = len(pos); det = []; ok = True
    seen = {}
    for i in range(k):
        key = pos[i]
        # players at identical positions are interchangeable: same deviation scores
        if key in seen:
            det.append(seen[key]); continue
        S = scores(n, pos, i)
        cur = S[pos[i]]; best = max(S); arg = S.index(best)
        d = (i, cur, best, arg); seen[key] = d; det.append(d)
        if best > cur:
            ok = False
            if early: return False, det
    return ok, det

def brute_scores(n, pos, i, L=None):
    k = len(pos); V = 1 << n
    if L is None: L = lcm(*range(1, k + 1))
    out = []
    for q in range(V):
        p2 = list(pos); p2[i] = q; s = 0
        for x in range(V):
            ds = [bin(x ^ p).count('1') for p in p2]
            m = min(ds)
            if ds[i] == m: s += L // ds.count(m)
        out.append(s)
    return out

def scores_lowmem(n, pos, i, L=None):
    """Same output as scores(); memory O(V) per radius (one radius at a time)."""
    k = len(pos); V = 1 << n
    if L is None: L = lcm(*range(1, k + 1))
    from math import comb as _c
    K = [[sum((-1) ** a * _c(w, a) * _c(n - w, j - a) for a in range(0, j + 1)) for w in range(n + 1)] for j in range(n + 1)]
    pc = [0] * V
    for x in range(1, V): pc[x] = pc[x >> 1] + (x & 1)
    others = [pos[j] for j in range(k) if j != i]
    M = [0] * V; Bv = [0] * V
    for x in range(V):
        ds = [pc[x ^ p] for p in others]
        m = min(ds); M[x] = m; Bv[x] = L // (ds.count(m) + 1)
    tot = [0] * V
    cum = 0
    for r in range(n + 1):
        U = [0] * V; nz = False
        for x in range(V):
            m = M[x]
            if m == r: U[x] += Bv[x]; nz = True
            elif m - 1 == r: U[x] += L - Bv[x]; nz = True
        if not nz: continue
        Ur = wht(U); del U
        hw = [sum(K[j][w] for j in range(r + 1)) for w in range(n + 1)]
        for w in range(V): tot[w] += Ur[w] * hw[pc[w]]
        del Ur
    S = wht(tot)
    return [s // V for s in S]

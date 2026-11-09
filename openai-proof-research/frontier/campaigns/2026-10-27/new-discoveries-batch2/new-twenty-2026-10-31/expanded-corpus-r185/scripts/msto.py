"""Exact mean subtree order tools (MathDB 344494, Cameron-Mol weaker conjecture).
mu(G) = R/N, N = #subtrees (incl. single vertices), R = sum of orders.
Subtrees of G+uv containing uv <-> ordered pairs of vertex-disjoint subtrees (T_u ∋ u, T_v ∋ v) of G.
So N(G+e) = N + A, R(G+e) = R + B with A = sum tau(S)tau(S'), B = sum tau tau (|S|+|S'|) over disjoint S∋u, S'∋v,
tau(S) = number of spanning trees of G[S] (0 if disconnected).
"""
from fractions import Fraction

def det_int(M):
    # Bareiss fraction-free determinant of integer matrix
    n = len(M)
    if n == 0: return 1
    A = [row[:] for row in M]; sign = 1; prev = 1
    for k in range(n - 1):
        if A[k][k] == 0:
            for r in range(k + 1, n):
                if A[r][k] != 0:
                    A[k], A[r] = A[r], A[k]; sign = -sign; break
            else:
                return 0
        akk = A[k][k]
        for i in range(k + 1, n):
            aik = A[i][k]
            Ai = A[i]; Ak = A[k]
            for j in range(k + 1, n):
                Ai[j] = (Ai[j] * akk - aik * Ak[j]) // prev
        prev = akk
    return sign * A[n - 1][n - 1]

def tau_table(n, adj):
    """adj: list of bitmasks. returns dict mask->tau for connected masks (tau>0)."""
    T = {}
    for S in range(1, 1 << n):
        vs = [i for i in range(n) if S >> i & 1]
        k = len(vs)
        if k == 1: T[S] = 1; continue
        # connectivity check
        seen = 1 << vs[0]; stack = [vs[0]]
        while stack:
            x = stack.pop(); nb = adj[x] & S & ~seen
            while nb:
                b = nb & -nb; nb ^= b; y = b.bit_length() - 1; seen |= b; stack.append(y)
        if seen != S: continue
        idx = {v: i for i, v in enumerate(vs)}
        M = [[0] * (k - 1) for _ in range(k - 1)]
        for a in range(1, k):
            va = vs[a]; nbm = adj[va] & S
            M[a - 1][a - 1] = bin(nbm).count('1')
            nb = nbm
            while nb:
                b = nb & -nb; nb ^= b; y = b.bit_length() - 1
                j = idx[y]
                if j >= 1: M[a - 1][j - 1] = -1
        T[S] = det_int(M)
    return T

def NR(T):
    N = sum(T.values()); R = sum(bin(S).count('1') * t for S, t in T.items())
    return N, R

def pair_sums(n, T, u, v):
    full = (1 << n) - 1
    bu, bv = 1 << u, 1 << v
    Su = [(S, t, bin(S).count('1')) for S, t in T.items() if S & bu and not S & bv]
    # index subtrees containing v by mask
    Sv = [(S, t, bin(S).count('1')) for S, t in T.items() if S & bv and not S & bu]
    A = 0; B = 0
    # group Sv by mask for disjointness test; brute force with early filter
    for S, t, c in Su:
        for S2, t2, c2 in Sv:
            if S & S2: continue
            p = t * t2; A += p; B += p * (c + c2)
    return A, B

def deltas(n, adj, T=None):
    if T is None: T = tau_table(n, adj)
    N, R = NR(T)
    out = []
    for u in range(n):
        for v in range(u + 1, n):
            if adj[u] >> v & 1: continue
            A, B = pair_sums(n, T, u, v)
            # mu(G+e) - mu(G) sign = sign(B*N - A*R)
            d = Fraction(R + B, N + A) - Fraction(R, N)
            out.append(((u, v), d))
    return Fraction(R, N), out

def from_edges(n, edges):
    adj = [0] * n
    for a, b in edges: adj[a] |= 1 << b; adj[b] |= 1 << a
    return adj

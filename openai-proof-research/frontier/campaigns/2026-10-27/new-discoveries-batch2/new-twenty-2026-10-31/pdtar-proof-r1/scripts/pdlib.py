"""Small exact helpers for power domination (PD) on graphs given as adjacency bitmasks.
Vertices 0..n-1; A = 0..s-1, B = s..s+t-1.  Pure python, no dependencies."""
import itertools

def closure(n, adj, S):
    """Observed set from S (bitmask): domination step N[S], then zero forcing to a fixpoint."""
    O = S
    for v in range(n):
        if S >> v & 1:
            O |= adj[v]
    changed = True
    while changed:
        changed = False
        for u in range(n):
            if O >> u & 1:
                un = adj[u] & ~O
                if un and un & (un - 1) == 0:
                    O |= un; changed = True
    return O

def is_pd(n, adj, S):
    return closure(n, adj, S) == (1 << n) - 1

def closed_nbhd(n, adj, S):
    O = S
    for v in range(n):
        if S >> v & 1:
            O |= adj[v]
    return O

def is_fort(n, adj, F):
    if F == 0:
        return False
    for v in range(n):
        if not (F >> v & 1):
            c = adj[v] & F
            if c and c & (c - 1) == 0:
                return False
    return True

def pd_family(n, adj):
    return frozenset(S for S in range(1 << n) if is_pd(n, adj, S))

def kst_adj(s, t):
    n = s + t; adj = [0] * n
    for a in range(s):
        for b in range(s, n):
            adj[a] |= 1 << b; adj[b] |= 1 << a
    return n, adj

def from_edges(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v; adj[v] |= 1 << u
    return adj

def edges_of(n, adj):
    return [(u, v) for u in range(n) for v in range(u + 1, n) if adj[u] >> v & 1]

def same_family_as_kst(s, t, adj):
    """Exact test via minimal PD sets / maximal non-PD sets of K_{s,t} (PD is up-closed), valid for s,t >= 2."""
    n = s + t; A = range(s); B = range(s, n)
    bit = lambda c: sum(1 << v for v in c)
    for a in A:
        for b in B:
            if not is_pd(n, adj, (1 << a) | (1 << b)):
                return False, ('pair', a, b)
    for c in itertools.combinations(A, s - 1):
        if not is_pd(n, adj, bit(c)):
            return False, ('A-1', c)
    for c in itertools.combinations(B, t - 1):
        if not is_pd(n, adj, bit(c)):
            return False, ('B-1', c)
    for c in itertools.combinations(A, s - 2):
        if is_pd(n, adj, bit(c)):
            return False, ('A-2 is PD', c)
    for c in itertools.combinations(B, t - 2):
        if is_pd(n, adj, bit(c)):
            return False, ('B-2 is PD', c)
    return True, None

def all_forts(n, adj):
    return [F for F in range(1, 1 << n) if is_fort(n, adj, F)]

def minimal_forts(n, adj):
    fs = all_forts(n, adj)
    return [F for F in fs if not any(G != F and G & F == G for G in fs)]

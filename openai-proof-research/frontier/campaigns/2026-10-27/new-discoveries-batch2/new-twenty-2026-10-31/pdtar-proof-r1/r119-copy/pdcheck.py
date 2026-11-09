"""Brute-force power domination family of a graph; decode a cadical model for pdsat.py."""
import sys, itertools
def closure(n, adj, S):
    O = set(S)
    for u in S: O |= adj[u]
    ch = True
    while ch:
        ch = False
        for u in list(O):
            un = [w for w in adj[u] if w not in O]
            if len(un) == 1: O.add(un[0]); ch = True
    return O
def family(n, adj):
    return {frozenset(S) for k in range(n + 1) for S in itertools.combinations(range(n), k) if len(closure(n, adj, S)) == n}
def kst(s, t):
    n = s + t; adj = [set() for _ in range(n)]
    for a in range(s):
        for b in range(s, n): adj[a].add(b); adj[b].add(a)
    return n, adj
def decode(s, t, logf):
    n = s + t; vals = set()
    for l in open(logf):
        if l.startswith('v '): vals |= {int(x) for x in l.split()[1:] if int(x) > 0}
    adj = [set() for _ in range(n)]; k = 0
    for u, v in itertools.combinations(range(n), 2):
        k += 1
        if k in vals: adj[u].add(v); adj[v].add(u)
    return n, adj
if __name__ == '__main__':
    s, t = int(sys.argv[1]), int(sys.argv[2])
    n, adj = decode(s, t, sys.argv[3])
    print('edges', sorted((u, v) for u in range(n) for v in adj[u] if u < v))
    print('same family as K_{s,t}:', family(n, adj) == family(*kst(s, t)))

"""Small library of cubic (multi)graph constructions, edge lists over 0..n-1."""
import itertools

def petersen():
    E = [(i, (i + 1) % 5) for i in range(5)] + [(i, i + 5) for i in range(5)] + [(5 + i, 5 + (i + 2) % 5) for i in range(5)]
    return 10, E

def relabel(n, E):
    vs = sorted(set(itertools.chain(*E)))
    m = {v: i for i, v in enumerate(vs)}
    return len(vs), [(m[u], m[v]) for u, v in E]

def tri(n, E, v):
    """replace vertex v by a triangle"""
    E2 = []; t = [v, n, n + 1]; c = 0
    for (a, b) in E:
        if a == v: E2.append((t[c], b)); c += 1
        elif b == v: E2.append((a, t[c])); c += 1
        else: E2.append((a, b))
    E2 += [(v, n), (n, n + 1), (n + 1, v)]
    return n + 2, E2

def digon_on(n, E, k):
    """replace edge k=uv by u-x, x=y (double), y-v"""
    u, v = E[k]; x, y = n, n + 1
    E2 = E[:k] + E[k + 1:] + [(u, x), (x, y), (x, y), (y, v)]
    return n + 2, E2

def two_sum(n1, E1, k1, n2, E2, k2):
    a, b = E1[k1]; c, d = E2[k2]
    E = [e for i, e in enumerate(E1) if i != k1] + [(u + n1, v + n1) for i, (u, v) in enumerate(E2) if i != k2]
    E += [(a, c + n1), (b, d + n1)]
    return n1 + n2, E

def dot(n1, E1, k1, k2, n2, E2, kxy):
    """dot product: remove independent edges k1=ab, k2=cd from G1, remove adjacent vertices x,y
    (edge kxy) from G2, join a,b to x's other nbrs and c,d to y's other nbrs."""
    a, b = E1[k1]; c, d = E1[k2]
    assert len({a, b, c, d}) == 4
    x, y = E2[kxy]
    xn = [ (v if u == x else u) for (u, v) in E2 if x in (u, v) and {u, v} != {x, y}]
    yn = [ (v if u == y else u) for (u, v) in E2 if y in (u, v) and {u, v} != {x, y}]
    assert len(xn) == 2 and len(yn) == 2
    E = [e for i, e in enumerate(E1) if i not in (k1, k2)]
    E += [(u + n1, v + n1) for (u, v) in E2 if x not in (u, v) and y not in (u, v)]
    E += [(a, xn[0] + n1), (b, xn[1] + n1), (c, yn[0] + n1), (d, yn[1] + n1)]
    return relabel(n1 + n2, E)

def flower(k):
    a = lambda i: 4 * (i % k); b = lambda i: 4 * (i % k) + 1; c = lambda i: 4 * (i % k) + 2; d = lambda i: 4 * (i % k) + 3
    E = []
    for i in range(k):
        E += [(a(i), b(i)), (a(i), c(i)), (a(i), d(i)), (b(i), b(i + 1))]
    for i in range(k - 1):
        E += [(c(i), c(i + 1)), (d(i), d(i + 1))]
    E += [(c(k - 1), d(0)), (d(k - 1), c(0))]
    return 4 * k, E

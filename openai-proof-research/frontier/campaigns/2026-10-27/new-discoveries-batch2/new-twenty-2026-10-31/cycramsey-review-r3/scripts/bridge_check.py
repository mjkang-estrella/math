"""Exhaustively enumerate (up to rotation) all 2-colourings of K_n with colour-1 max degree <= a-2
and no colour-2 cyclic P_b^mon; for each, test whether a colour-2 cyclic C_{b-1}^mon exists, and
check the bridge inequality 2(n-(b-1)) <= (b-1)(a-2) whenever it does.
Usage: bridge_check.py a b n [maxsols]"""
import sys
a, b, n = map(int, sys.argv[1:4]); maxsols = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9
t = a - 2
edges = []
for d in range(1, n // 2 + 1):
    for i in range(n):
        j = (i + d) % n; e = (min(i, j), max(i, j))
        if e not in edges: edges.append(e)
adj2 = [0] * n; deg1 = [0] * n; redset = set()
def has_path(L):
    for s in range(n):
        E = [0] * (L + 1)
        for i in range(n):
            y = (s + i) % n; m = adj2[y]; Ly = 1
            for l in range(L - 1, 0, -1):
                if m & E[l]: Ly = l + 1; break
            if Ly >= L: return True
            for l in range(1, Ly + 1): E[l] |= 1 << y
    return False
def has_cycle(k):  # clockwise cycle on k vertices, all cyclically consecutive pairs colour 2
    for s in range(n):
        P = {1: 1 << s}
        for l in range(2, k + 1): P[l] = 0
        for i in range(1, n):
            y = (s + i) % n
            for l in range(k, 1, -1):
                if adj2[y] & P[l - 1]: P[l] |= 1 << y
        if P[k] & adj2[s]: return True
    return False
def lexmin_ok():
    pat = [1 if (min(i, (i + 1) % n), max(i, (i + 1) % n)) in redset else 0 for i in range(n)]
    return all(pat <= pat[r:] + pat[:r] for r in range(1, n))
stats = {"solutions": 0, "with_cycle": 0, "violations": 0}
def rec(k):
    if stats["solutions"] >= maxsols: return
    if k == n and not lexmin_ok(): return
    if k == len(edges):
        stats["solutions"] += 1
        if has_cycle(b - 1):
            stats["with_cycle"] += 1
            if not 2 * (n - (b - 1)) <= (b - 1) * (a - 2): stats["violations"] += 1
        return
    u, v = edges[k]
    adj2[u] |= 1 << v; adj2[v] |= 1 << u
    if not has_path(b): rec(k + 1)
    adj2[u] &= ~(1 << v); adj2[v] &= ~(1 << u)
    if deg1[u] < t and deg1[v] < t:
        deg1[u] += 1; deg1[v] += 1; redset.add((u, v))
        rec(k + 1)
        deg1[u] -= 1; deg1[v] -= 1; redset.discard((u, v))
rec(0)
ineq = 2 * (n - (b - 1)) <= (b - 1) * (a - 2)
print(f"a={a} b={b} n={n} inequality_holds={ineq} {stats}" + (" (capped)" if stats['solutions'] >= maxsols else ""))

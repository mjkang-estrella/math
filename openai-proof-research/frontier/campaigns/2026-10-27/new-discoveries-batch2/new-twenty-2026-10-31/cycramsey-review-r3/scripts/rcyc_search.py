"""Exhaustive pure-Python backtracking: does a 2-colouring of K_n exist with no colour-1
cyclic S_a and no colour-2 cyclic P_b^mon?  (Criteria validated against the literal
definition by defcheck.py.)  Colour 1 = 'red' sparse graph, max degree <= a-2.
Edges are branched in order of cyclic chord length; rotation symmetry broken by requiring
the colour pattern of length-1 chords to be lexicographically minimal among its rotations.
Usage: rcyc_search.py a b n   -> prints SAT (with witness) or UNSAT and node count."""
import sys
sys.setrecursionlimit(10000)
a, b, n = map(int, sys.argv[1:4])
t = a - 2
edges = []
for d in range(1, n // 2 + 1):
    for i in range(n):
        j = (i + d) % n
        e = (min(i, j), max(i, j))
        if e not in edges:
            edges.append(e)
assert len(edges) == n * (n - 1) // 2
n1 = n  # number of length-1 chords (n >= 3)
adj2 = [0] * n      # decided colour-2 adjacency bitmasks
deg1 = [0] * n
red = []
nodes = 0
def has_path():
    # clockwise path on b vertices using decided colour-2 edges
    for s in range(n):
        E = [0] * (b + 1)   # E[l] = mask of processed vertices with longest path ending there >= l
        for i in range(n):
            y = (s + i) % n
            m = adj2[y]
            L = 1
            for l in range(b - 1, 0, -1):
                if m & E[l]:
                    L = l + 1
                    break
            if L >= b:
                return True
            bit = 1 << y
            for l in range(1, L + 1):
                E[l] |= bit
    return False
def lexmin_ok():
    pat = []
    for i in range(n):
        u, v = i, (i + 1) % n
        pat.append(1 if (min(u, v), max(u, v)) in redset else 0)
    # pattern indexed by chord (i,i+1); require minimal among rotations
    return all(pat <= pat[r:] + pat[:r] for r in range(1, n))
redset = set()
found = None
def rec(k):
    global nodes, found
    nodes += 1
    if k == n1 and not lexmin_ok():
        return False
    if k == len(edges):
        found = sorted(redset)
        return True
    u, v = edges[k]
    # try colour 2
    adj2[u] |= 1 << v; adj2[v] |= 1 << u
    if not has_path():
        if rec(k + 1):
            return True
    adj2[u] &= ~(1 << v); adj2[v] &= ~(1 << u)
    # try colour 1
    if deg1[u] < t and deg1[v] < t:
        deg1[u] += 1; deg1[v] += 1; redset.add((u, v))
        if rec(k + 1):
            return True
        deg1[u] -= 1; deg1[v] -= 1; redset.discard((u, v))
    return False
ok = rec(0)
print(f"a={a} b={b} n={n} {'SAT' if ok else 'UNSAT'} nodes={nodes}" + (f" red={found}" if ok else ""))

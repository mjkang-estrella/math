"""Brute-force k-semi-transitivity of line graphs (Akbar-Akrobotu-Brewer arXiv:2108.02363 definitions):
an acyclic orientation (= induced by a linear order) is 3-semi-transitive if it has no shortcut on 4 vertices,
i.e. no directed path a->b->c->d with arc a->d but missing a->c or b->d; semi-transitive = no shortcut of any length.
usage: semitrans.py GRAPHNAME   (W4 = wheel C4+hub, K5)"""
import sys, itertools, json
name = sys.argv[1]
if name == 'W4': E = [(0,1),(1,2),(2,3),(3,0),(4,0),(4,1),(4,2),(4,3)]
elif name == 'K5': E = list(itertools.combinations(range(5), 2))
m = len(E); adj = [[False]*m for _ in range(m)]
for i in range(m):
    for j in range(m):
        if i != j and set(E[i]) & set(E[j]): adj[i][j] = True
def three_st(order):
    pos = {v: k for k, v in enumerate(order)}
    arc = lambda u, v: adj[u][v] and pos[u] < pos[v]
    for a in range(m):
        for d in range(m):
            if not arc(a, d): continue
            for b in range(m):
                if not arc(a, b): continue
                for c in range(m):
                    if c in (a, d) or not (arc(b, c) and arc(c, d)): continue
                    if not (arc(a, c) and arc(b, d)): return False
    return True
cnt = 0; found = None
for order in itertools.permutations(range(m)):
    cnt += 1
    if three_st(order): found = order; break
print(json.dumps(dict(graph=name, line_graph_vertices=m, line_graph_edges=sum(map(sum, adj))//2, orders_checked=cnt, three_semi_transitive_order=found)))

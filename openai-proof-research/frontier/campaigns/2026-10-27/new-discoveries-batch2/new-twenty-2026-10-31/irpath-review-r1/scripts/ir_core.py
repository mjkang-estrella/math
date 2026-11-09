"""Independent IR-graph computation from the Mynhardt-Roux definitions (own code).
Private neighbour: w in N[v] - N[D - {v}] (closed neighbourhoods).
Irredundant: every v in D has a D-private neighbour (empty set irredundant).
IR(G): max |D| irredundant. IR-set: irredundant with |D| = IR(G).
G(IR): vertices IR-sets; D ~ D' iff exists u in D, v in D', uv in E(G), D' = (D - {u}) | {v}.
"""
from itertools import combinations

def closed_nbhd(n, edges):
    N = [{v} for v in range(n)]
    for a, b in edges:
        N[a].add(b); N[b].add(a)
    return N

def private_nbrs(N, D, v):
    others = set()
    for u in D:
        if u != v:
            others |= N[u]
    return N[v] - others

def irredundant(N, D):
    return all(private_nbrs(N, D, v) for v in D)

def all_irredundant(n, N):
    return [frozenset(D) for k in range(n + 1) for D in combinations(range(n), k) if irredundant(N, D)]

def ir_graph(n, edges):
    N = closed_nbhd(n, edges)
    E = {frozenset(e) for e in edges}
    irr = all_irredundant(n, N)
    IR = max(len(D) for D in irr)
    sets = sorted((D for D in irr if len(D) == IR), key=lambda s: sorted(s))
    adj = []
    for i, j in combinations(range(len(sets)), 2):
        A, B = sets[i], sets[j]
        ok = False
        for u in A:
            for v in B:
                if frozenset((u, v)) in E and B == (A - {u}) | {v}:
                    ok = True
        # check symmetry of the source relation explicitly
        ok2 = any(frozenset((u, v)) in E and A == (B - {u}) | {v} for u in B for v in A)
        assert ok == ok2
        if ok:
            adj.append((i, j))
    return IR, sets, adj, irr

def classify(m, adj):
    deg = [0] * m
    nb = [[] for _ in range(m)]
    for i, j in adj:
        deg[i] += 1; deg[j] += 1; nb[i].append(j); nb[j].append(i)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in nb[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    conn = len(seen) == m
    if conn and m >= 2 and len(adj) == m - 1 and max(deg) <= 2:
        return "P%d" % m
    if conn and m >= 3 and len(adj) == m and all(d == 2 for d in deg):
        return "C%d" % m
    if m == 1:
        return "P1"
    return None

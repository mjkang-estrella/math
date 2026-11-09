"""335271: for a=0 solutions (pattern BNBN...B) print the two spanning trees on B (T_out from out-pairs of N
vertices, T_in from in-pairs), their bipartition colours, pairing pi, and cycle types of h_{s,t} for all s,t.
usage: kinout_trees.py FILE.json [maxsol]"""
import sys, json
f = sys.argv[1]
mx = int(sys.argv[2]) if len(sys.argv) > 2 else 3
d = json.load(open(f))
shown = 0


def colour(B, edges):
    adj = {b: [] for b in B}
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = {B[0]: 0}
    st = [B[0]]
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in col:
                col[v] = 1 - col[u]
                st.append(v)
    return col, adj


def rooted_far(adj, root, edge):
    # endpoint of edge farther from root
    u, v = edge
    dist = {root: 0}
    st = [root]
    while st:
        a = st.pop()
        for b in adj[a]:
            if b not in dist:
                dist[b] = dist[a] + 1
                st.append(b)
    return u if dist[u] > dist[v] else v


for sol in d['found_first']:
    w = sol['pattern']
    if set(w) != {'B', 'N'}:
        continue
    n = len(w)
    B = [v for v in range(n) if w[v] == 'B']
    N = [v for v in range(n) if w[v] == 'N']
    outp = {x: [] for x in N}
    inp = {x: [] for x in N}
    for u, v in sol['arcs']:
        if u in outp:
            outp[u].append(v)
        if v in inp:
            inp[v].append(u)
    Tout = [tuple(outp[x]) for x in N]
    Tin = [tuple(inp[x]) for x in N]
    co, ao = colour(B, Tout)
    ci, ai = colour(B, Tin)
    table = {}
    for s in B:
        row = []
        for t in B:
            succ = {x: rooted_far(ao, s, tuple(outp[x])) for x in N}
            pred = {x: rooted_far(ai, t, tuple(inp[x])) for x in N}
            pinv = {pred[x]: x for x in N}
            h = {}
            for b in B:
                h[b] = s if b == t else succ[pinv[b]]
            seen = set()
            cyc = []
            for b in B:
                if b in seen:
                    continue
                L = 0
                c = b
                while c not in seen:
                    seen.add(c)
                    c = h[c]
                    L += 1
                cyc.append(L)
            row.append(len(cyc))
        table[s] = row
    print('pattern', w, 'B', B)
    print(' T_out (out-pairs per N):', dict(zip(N, Tout)), 'colours', co)
    print(' T_in  (in-pairs per N):', dict(zip(N, Tin)), 'colours', ci)
    print(' pairs', sol['pairs'])
    print(' #cycles of h_{s,t} (rows s, cols t in B order):')
    for s in B:
        print('   ', s, table[s])
    shown += 1
    if shown >= mx:
        break

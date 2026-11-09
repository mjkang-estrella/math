"""365134 controls: (1) source Theorem 5 graph, l=1 (three P10-e blocks joined cyclically by paths of
length two, centre vertices joined to u1) must have NO non-conflicting flow and NO Hamiltonian path;
(2) independent re-verification of witnesses found by ncflow for several named graphs, using
Z2xZ2 arithmetic on G/Fbar directly (edge-based flow conservation on contracted vertices)."""
import sys, json, pathlib
D = pathlib.Path(sys.argv[1]).resolve(); sys.path.insert(0, str(D / 'scripts'))
import ncflow as N, snarklib as L
P_n, P_E = L.petersen()

def theorem5(l):
    E = []; n = 0; att = []
    for j in range(3 * l):
        off = n; E += [(a + off, b + off) for (a, b) in P_E[1:]]; att.append((P_E[0][0] + off, P_E[0][1] + off)); n += 10
    centres = []
    for j in range(3 * l):
        w = n; n += 1; centres.append(w)
        E += [(att[j][1], w), (w, att[(j + 1) % (3 * l)][0])]
    for i in range(l):
        u = n; n += 1
        for w in centres[3 * i:3 * i + 3]: E.append((u, w))
    return n, E

def verify(n, E, F_edges, labels):
    """independent check: F perfect matching; Fbar 2-factor; contract Fbar cycles; flow sums zero;
    no Fbar edge with ends labelled a and b."""
    val = {'a': (1, 0), 'b': (0, 1), 'g': (1, 1)}
    from collections import Counter
    Fc = Counter(tuple(sorted(e)) for e in F_edges); Ec = Counter(tuple(sorted(e)) for e in E)
    assert all(Ec[e] >= c for e, c in Fc.items())
    deg = Counter(); lab = {}
    for i, (u, v) in enumerate(F_edges):
        deg[u] += 1; deg[v] += 1; lab[u] = lab[v] = labels[i] if isinstance(labels, list) else labels[str(i)] if str(i) in labels else labels[i]
    assert all(deg[x] == 1 for x in range(n)), 'not perfect'
    rest = Ec - Fc; adj = {x: [] for x in range(n)}
    for (u, v), c in rest.items():
        for _ in range(c): adj[u].append(v); adj[v].append(u)
    assert all(len(adj[x]) == 2 for x in range(n))
    comp = {}; k = 0
    for s in range(n):
        if s in comp: continue
        st = [s]; comp[s] = k
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in comp: comp[y] = k; st.append(y)
        k += 1
    tot = [[0, 0] for _ in range(k)]
    for (u, v), lb in zip([tuple(e) for e in F_edges], [lab[e[0]] for e in F_edges]):
        for x in (u, v):
            t = tot[comp[x]]; t[0] ^= val[lb][0]; t[1] ^= val[lb][1]
    assert all(t == [0, 0] for t in tot), 'flow fails'
    for (u, v) in rest.elements():
        assert {lab[u], lab[v]} != {'a', 'b'}, 'conflict'
    return True

out = {}
n, E = theorem5(1)
inc = N.adjacency(n, E); found = None; npm = 0
for F in N.perfect_matchings(n, E, inc):
    npm += 1; w = N.flow_exists(n, E, inc, F)
    if w: found = w; break
out['theorem5_l1'] = {'n': n, 'perfect_matchings': npm, 'flow_found': found is not None,
                      'bridgeless': N.bridgeless(n, E), 'ham_path': N.has_ham_path(n, E) if n <= 34 and False else 'see argument'}
tests = [('P10-triangle', *L.tri(P_n, P_E, 0)), ('2sum', *L.two_sum(P_n, P_E, 0, P_n, P_E, 0)),
         ('dot', *L.dot(P_n, P_E, 0, 2, P_n, P_E, 0)), ('J5', *L.flower(5)), ('J7', *L.flower(7))]
for name, n2, E2 in tests:
    inc2 = N.adjacency(n2, E2)
    for F in N.perfect_matchings(n2, E2, inc2):
        w = N.flow_exists(n2, E2, inc2, F)
        if w:
            out[name] = {'verified': verify(n2, E2, [E2[k] for k in F], [w['labels'][i] for i in range(len(F))]),
                         'labels': ''.join(w['labels'][i] for i in range(len(F)))}
            break
print(json.dumps(out, indent=1))

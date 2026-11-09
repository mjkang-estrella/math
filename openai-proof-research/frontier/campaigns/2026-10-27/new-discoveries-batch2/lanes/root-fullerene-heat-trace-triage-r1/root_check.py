import json, math
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations

p = Path(__file__).parent
cert = json.loads((p / 'graph-certificates.json').read_text())

def connected(adj, removed=()):
    remaining = set(range(len(adj))) - set(removed)
    if not remaining:
        return True
    seen = {min(remaining)}
    todo = list(seen)
    while todo:
        v = todo.pop()
        for w in adj[v]:
            if w in remaining and w not in seen:
                seen.add(w)
                todo.append(w)
    return seen == remaining

def three_connected(adj):
    assert connected(adj)
    for v in range(len(adj)):
        assert connected(adj, [v])
    for pair in combinations(range(len(adj)), 2):
        assert connected(adj, pair)

def graph(name):
    edges = json.loads((p / (name + '-edges.json')).read_text())
    assert len(edges) == len({tuple(sorted(e)) for e in edges}) == 90
    adj = [set() for _ in range(32)]
    for a, b in edges:
        assert 0 <= a < b < 32
        adj[a].add(b)
        adj[b].add(a)
    assert sorted(map(len, adj)) == [5]*12 + [6]*20
    faces = cert[name]['faces']
    assert len(faces) == 60
    darts = {}
    links = [{u: set() for u in adj[v]} for v in range(32)]
    for i, face in enumerate(faces):
        assert len(face) == len(set(face)) == 3
        for j in range(3):
            a, b, c = face[j], face[(j+1)%3], face[(j+2)%3]
            assert b in adj[a] and (a,b) not in darts
            darts[a,b] = i
            links[a][b].add(c)
            links[a][c].add(b)
    assert len(darts) == 180
    for v, link in enumerate(links):
        assert all(len(link[u]) == 2 for u in link)
        nodes = sorted(link)
        ix = {u:i for i,u in enumerate(nodes)}
        assert connected([{ix[w] for w in link[u]} for u in nodes])
    dual = [set() for _ in faces]
    for (a,b), i in darts.items():
        j = darts[b,a]
        assert i != j
        dual[i].add(j)
    assert all(len(x) == 3 for x in dual)
    assert 32-90+60 == 2
    three_connected(adj)
    three_connected(dual)
    return adj

graphs = {s: graph(s) for s in ['G','H']}

def trace_series(adj, off, diagonal, denominator):
    rows = [[int(i == j) for j in range(32)] for i in range(32)]
    terms = [32]
    total = F(32)
    divisor = 1
    for k in range(1, 91):
        new = [[0]*32 for _ in range(32)]
        for i in range(32):
            for j, value in enumerate(rows[i]):
                if value:
                    new[i][j] += value * diagonal * len(adj[j])
                    for w in adj[j]:
                        new[i][w] += value * off
        rows = new
        tr = sum(rows[i][i] for i in range(32))
        terms.append(tr)
        divisor *= denominator*k
        total += F(tr, divisor)
    R = F(6*(off+diagonal), denominator)
    error = 32 * 3**math.ceil(R) * R**91 / math.factorial(91)
    return total, error, terms[6]

results = {}
for label, args, lower, upper in [
    ('beta=1/50', (45,1,50), F(1,1000), F(1,500)),
    ('beta=9/10', (9,9,10), F(-2), F(-1))]:
    g, eg, mg = trace_series(graphs['G'], *args)
    h, eh, mh = trace_series(graphs['H'], *args)
    lo, hi = g-h-eh, g-h+eg
    assert lower < lo <= hi < upper
    results[label] = {'lower_bound':str(lo), 'upper_bound':str(hi),
                      'coarse_interval':[str(lower),str(upper)],
                      'sixth_integer_moments':[mg,mh]}
assert results['beta=1/50']['sixth_integer_moments'] == [540051518791920,540051567999420]
out = {'status':'PASS','graphs':'two connected oriented triangular sphere complexes; primal and dual 3-connected',
       'endpoint_checks':results,'scope':'finite graph and rational arithmetic certificate; continuity and surface/convexity theorems remain ordinary mathematics'}
(p/'root-check-result.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: graph complexes, both 3-connectivity checks, rational trace signs, distinct sixth moments')

"""Decode r119 ablation models (first C(n,2) CNF vars = edges) for each (s,t) guess; report which K_{s,t} constraint fails."""
import sys, itertools
sys.path.insert(0, 'scripts')
import pdlib
for m in ['noA', 'noB', 'nopd', 'pairsonly']:
    vals = set()
    for l in open(f'r119-copy/abl-{m}.log'):
        if l.startswith('v '): vals |= {int(x) for x in l.split()[1:] if int(x) > 0}
    for (s, t) in [(3, 4), (4, 4), (3, 5), (4, 5)]:
        n = s + t; edges = [e for k, e in enumerate(itertools.combinations(range(n), 2), 1) if k in vals]
        adj = pdlib.from_edges(n, edges)
        if any(a == 0 for a in adj): continue
        ok, why = pdlib.same_family_as_kst(s, t, adj)
        print(m, (s, t), 'edges', edges, 'same?', ok, why)

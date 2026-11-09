"""335271: for every found solution (any a) report max degree of T_out (edges = out-pairs of X=I∪N vertices, on I∪B)
and T_in (edges = in-pairs of Y=O∪N vertices, on O∪B), and check both are spanning trees.
usage: kinout_treedeg.py FILE.json [...]"""
import sys, json
from collections import Counter
for f in sys.argv[1:]:
    d = json.load(open(f))
    stats = Counter()
    for sol in d['found_first']:
        w = sol['pattern']
        n = len(w)
        X = [v for v in range(n) if w[v] in 'IN']
        Y = [v for v in range(n) if w[v] in 'ON']
        outp = {x: [] for x in X}
        inp = {y: [] for y in Y}
        for u, v in sol['arcs']:
            if u in outp:
                outp[u].append(v)
            if v in inp:
                inp[v].append(u)
        res = []
        for pairs, verts in ((outp, [v for v in range(n) if w[v] in 'IB']), (inp, [v for v in range(n) if w[v] in 'OB'])):
            deg = Counter()
            par = {v: v for v in verts}

            def find(a):
                while par[a] != a:
                    par[a] = par[par[a]]
                    a = par[a]
                return a
            tree = True
            for e in pairs.values():
                assert len(e) == 2
                a, b = find(e[0]), find(e[1])
                if a == b:
                    tree = False
                par[a] = b
                deg[e[0]] += 1
                deg[e[1]] += 1
            res.append((tree, max(deg.values())))
        stats[(w.count('I'), tuple(res))] += 1
    print(f.rsplit('/', 1)[-1], dict(stats))

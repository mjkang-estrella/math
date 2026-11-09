import sys, json, collections
cnt = collections.Counter(); viol = []; eq = collections.Counter(); ex = {}
for fn in sys.argv[1:]:
    for line in open(fn):
        n, adj, d, s = json.loads(line)
        cnt[(n, d)] += 1
        if 3 * d > 2 * n: viol.append((n, adj, d, s))
        if 3 * d == 2 * n:
            eq[n] += 1; ex.setdefault(n, []).append(adj) if len(ex.get(n, [])) < 3 else None
print('graphs by (n, D-value):', sorted(cnt.items()))
print('violations:', len(viol), viol[:3])
print('equality cases 3D=2n by n:', dict(eq))
for n in ex: print(' eq examples n', n, ex[n])

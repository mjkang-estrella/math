import sys, json, collections
best = collections.defaultdict(list)
for fn in sys.argv[1:]:
    for line in open(fn):
        n, adj, d, s = json.loads(line)
        # connected only
        seen = 1; fr = 1
        while fr:
            nb = 0
            for v in range(n):
                if fr >> v & 1: nb |= adj[v]
            fr = nb & ~seen; seen |= nb
        if seen != (1 << n) - 1: continue
        best[n].append((3 * s - 2 * n, s - d, d, s, adj))
for n in sorted(best):
    L = sorted(best[n], key=lambda x: (-x[0], -x[1]))
    print('n', n, 'connected', len(L), 'max 3S-2n', L[0][0], 'max S-D', max(x[1] for x in L))
    for x in L[:6]: print('   3S-2n', x[0], 'D', x[2], 'S', x[3], 'adj', x[4])

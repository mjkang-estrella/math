"""Convert 'P n edges' lines (possibly prefixed) into raw tree lines 'N u1 v1 ...' by attaching a
pendant leaf to every leaf of the piece (so the piece is the unique piece of the tree)."""
import sys
for line in sys.stdin:
    t = line.split()
    if 'P' not in t: continue
    t = t[t.index('P'):]
    n = int(t[1]); E = [(int(t[2 + 2 * i]), int(t[3 + 2 * i])) for i in range(n - 1)]
    deg = [0] * n
    for u, v in E: deg[u] += 1; deg[v] += 1
    TE = list(E); nn = n
    for v in range(n):
        if deg[v] == 1: TE.append((v, nn)); nn += 1
    print(nn, " ".join("%d %d" % e for e in TE))
